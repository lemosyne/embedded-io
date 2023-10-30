//! Blocking IO traits

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use core::fmt;

/// Error returned by [`Read::read_exact`]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum ReadExactError<E> {
    /// An EOF error was encountered before reading the exact amount of requested bytes.
    UnexpectedEof,
    /// Error returned by the inner Read.
    Other(E),
}

impl<E> From<E> for ReadExactError<E> {
    fn from(value: E) -> Self {
        Self::Other(value)
    }
}

impl<E: fmt::Debug> fmt::Display for ReadExactError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[cfg(feature = "std")]
impl<E: fmt::Debug> std::error::Error for ReadExactError<E> {}

/// Error returned by [`Write::write_fmt`]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum WriteFmtError<E> {
    /// An error was encountered while formatting.
    FmtError,
    /// Error returned by the inner Write.
    Other(E),
}

impl<E: fmt::Debug> fmt::Display for WriteFmtError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[cfg(feature = "std")]
impl<E: fmt::Debug> std::error::Error for WriteFmtError<E> {}

/// Blocking reader.
///
/// Semantics are the same as [`std::io::Read`], check its documentation for details.
pub trait Read: crate::Io {
    /// Pull some bytes from this source into the specified buffer, returning how many bytes were read.
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error>;

    /// Read the exact number of bytes required to fill `buf`.
    fn read_exact(&mut self, mut buf: &mut [u8]) -> Result<(), ReadExactError<Self::Error>> {
        while !buf.is_empty() {
            match self.read(buf) {
                Ok(0) => break,
                Ok(n) => buf = &mut buf[n..],
                Err(e) => return Err(ReadExactError::Other(e)),
            }
        }
        if !buf.is_empty() {
            Err(ReadExactError::UnexpectedEof)
        } else {
            Ok(())
        }
    }

    /// Read all bytes until EOF in this source, placing them into `buf`.
    ///
    /// If successful, this function will return the total number of bytes read.
    #[cfg(feature = "alloc")]
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> Result<usize, Self::Error> {
        let mut count = 0;
        let mut block = [0; 4096];

        loop {
            match self.read(&mut block) {
                Ok(0) => break,
                Ok(n) => {
                    count += n;
                    buf.extend(&block[..n]);
                }
                Err(e) => return Err(e),
            }
        }

        Ok(count)
    }
}

/// Blocking buffered reader.
///
/// Semantics are the same as [`std::io::BufRead`], check its documentation for details.
pub trait BufRead: crate::Io {
    /// Return the contents of the internal buffer, filling it with more data from the inner reader if it is empty.
    fn fill_buf(&mut self) -> Result<&[u8], Self::Error>;

    /// Tell this buffer that `amt` bytes have been consumed from the buffer, so they should no longer be returned in calls to `fill_buf`.
    fn consume(&mut self, amt: usize);
}

/// Blocking writer.
///
/// Semantics are the same as [`std::io::Write`], check its documentation for details.
pub trait Write: crate::Io {
    /// Write a buffer into this writer, returning how many bytes were written.
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error>;

    /// Flush this output stream, ensuring that all intermediately buffered contents reach their destination.
    fn flush(&mut self) -> Result<(), Self::Error>;

    /// Write an entire buffer into this writer.
    fn write_all(&mut self, mut buf: &[u8]) -> Result<(), Self::Error> {
        while !buf.is_empty() {
            match self.write(buf) {
                Ok(0) => panic!("zero-length write."),
                Ok(n) => buf = &buf[n..],
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }

    /// Write a formatted string into this writer, returning any error encountered.
    fn write_fmt(&mut self, fmt: fmt::Arguments<'_>) -> Result<(), WriteFmtError<Self::Error>> {
        // Create a shim which translates a Write to a fmt::Write and saves
        // off I/O errors. instead of discarding them
        struct Adapter<'a, T: Write + ?Sized + 'a> {
            inner: &'a mut T,
            error: Result<(), T::Error>,
        }

        impl<T: Write + ?Sized> fmt::Write for Adapter<'_, T> {
            fn write_str(&mut self, s: &str) -> fmt::Result {
                match self.inner.write_all(s.as_bytes()) {
                    Ok(()) => Ok(()),
                    Err(e) => {
                        self.error = Err(e);
                        Err(fmt::Error)
                    }
                }
            }
        }

        let mut output = Adapter {
            inner: self,
            error: Ok(()),
        };
        match fmt::write(&mut output, fmt) {
            Ok(()) => Ok(()),
            Err(..) => match output.error {
                // check if the error came from the underlying `Write` or not
                Err(e) => Err(WriteFmtError::Other(e)),
                Ok(()) => Err(WriteFmtError::FmtError),
            },
        }
    }
}

/// Blocking seek within streams.
///
/// Semantics are the same as [`std::io::Seek`], check its documentation for details.
pub trait Seek: crate::Io {
    /// Seek to an offset, in bytes, in a stream.
    fn seek(&mut self, pos: crate::SeekFrom) -> Result<u64, Self::Error>;

    /// Rewind to the beginning of a stream.
    fn rewind(&mut self) -> Result<(), Self::Error> {
        self.seek(crate::SeekFrom::Start(0))?;
        Ok(())
    }

    /// Returns the current seek position from the start of the stream.
    fn stream_position(&mut self) -> Result<u64, Self::Error> {
        self.seek(crate::SeekFrom::Current(0))
    }
}

impl<T: ?Sized + Read> Read for &mut T {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        T::read(self, buf)
    }
}

impl<T: ?Sized + BufRead> BufRead for &mut T {
    fn fill_buf(&mut self) -> Result<&[u8], Self::Error> {
        T::fill_buf(self)
    }

    fn consume(&mut self, amt: usize) {
        T::consume(self, amt)
    }
}

impl<T: ?Sized + Write> Write for &mut T {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        T::write(self, buf)
    }

    #[inline]
    fn flush(&mut self) -> Result<(), Self::Error> {
        T::flush(self)
    }
}

impl<T: ?Sized + Seek> Seek for &mut T {
    #[inline]
    fn seek(&mut self, pos: crate::SeekFrom) -> Result<u64, Self::Error> {
        T::seek(self, pos)
    }
}

/// Error returned by [`ReadAt::read_exact_at`]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum ReadExactAtError<E> {
    /// An EOF error was encountered before reading the exact amount of requested bytes.
    UnexpectedEof,
    /// Error returned by the inner ReadAt.
    Other(E),
}

/// Blocking positioned reader.
///
/// Semantics are the same as the [`std::os::unix::fs::FileExt`].
pub trait ReadAt: crate::Io {
    /// Reads a number of bytes starting from a given offset.
    /// The offset is relative to the start of the file and thus independent from the current cursor.
    /// The current file cursor is not affected by this function.
    /// It is not an error to return with a short read.
    fn read_at(&self, buf: &mut [u8], offset: u64) -> Result<usize, Self::Error>;

    /// Reads the exact number of byte required to fill buf from the given offset. The offset is
    /// relative to the start of the file and thus independent from the current cursor. The current
    /// file cursor is not affected by this function.
    #[cfg(feature = "alloc")]
    fn read_exact_at(
        &self,
        mut buf: &mut [u8],
        mut offset: u64,
    ) -> Result<(), ReadExactAtError<Self::Error>> {
        while !buf.is_empty() {
            match self.read_at(buf, offset) {
                Ok(0) => break,
                Ok(n) => {
                    let tmp = buf;
                    buf = &mut tmp[n..];
                    offset += n as u64;
                }
                Err(e) => return Err(ReadExactAtError::Other(e)),
            }
        }
        if !buf.is_empty() {
            Err(ReadExactAtError::UnexpectedEof)
        } else {
            Ok(())
        }
    }
}

/// Blocking positioned reader.
///
/// Semantics are the same as the [`std::os::unix::fs::FileExt`].
pub trait WriteAt: crate::Io {
    /// Writes a number of bytes starting from a given offset.
    /// Returns the number of bytes written.
    /// The offset is relative to the start of the file and thus independent from the current cursor.
    /// The current file cursor is not affected by this function.
    /// When writing beyond the end of the file, the file is appropriately extended and the intermediate bytes are initialized with the value 0.
    ///
    /// It is not an error to return a short write.
    fn write_at(&self, buf: &[u8], offset: u64) -> Result<usize, Self::Error>;

    /// Attempts to write an entire buffer starting from a given offset.
    /// The offset is relative to the start of the file and thus independent from the current cursor.
    /// The current file cursor is not affected by this function.
    /// This method will continuously call write_at until there is no more data to be written or an error of non-io::ErrorKind::Interrupted kind is returned. This method will not return until the entire buffer has been successfully written or such an error occurs.
    fn write_all_at(&self, mut buf: &[u8], mut offset: u64) -> Result<(), Self::Error> {
        while !buf.is_empty() {
            match self.write_at(buf, offset) {
                Ok(0) => panic!("zero-length write at."),
                Ok(n) => {
                    buf = &buf[n..];
                    offset += n as u64
                }
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }
}

/// Read is implemented for `&[u8]` by copying from the slice.
///
/// Note that reading updates the slice to point to the yet unread part.
/// The slice will be empty when EOF is reached.
impl Read for &[u8] {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        let amt = core::cmp::min(buf.len(), self.len());
        let (a, b) = self.split_at(amt);

        // First check if the amount of bytes we want to read is small:
        // `copy_from_slice` will generally expand to a call to `memcpy`, and
        // for a single byte the overhead is significant.
        if amt == 1 {
            buf[0] = a[0];
        } else {
            buf[..amt].copy_from_slice(a);
        }

        *self = b;
        Ok(amt)
    }
}

impl BufRead for &[u8] {
    #[inline]
    fn fill_buf(&mut self) -> Result<&[u8], Self::Error> {
        Ok(*self)
    }

    #[inline]
    fn consume(&mut self, amt: usize) {
        *self = &self[amt..];
    }
}

/// Write is implemented for `&mut [u8]` by copying into the slice, overwriting
/// its data.
///
/// Note that writing updates the slice to point to the yet unwritten part.
/// The slice will be empty when it has been completely overwritten.
///
/// If the number of bytes to be written exceeds the size of the slice, write operations will
/// return short writes: ultimately, `Ok(0)`; in this situation, `write_all` returns an error of
/// kind `ErrorKind::WriteZero`.
impl Write for &mut [u8] {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        let amt = core::cmp::min(buf.len(), self.len());
        let (a, b) = core::mem::replace(self, &mut []).split_at_mut(amt);
        a.copy_from_slice(&buf[..amt]);
        *self = b;
        Ok(amt)
    }

    #[inline]
    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

/// ReadAt is implemented for `&[u8]` by copying from the slice.
///
/// Short reads will occur if the number of bytes to read exceeds the distance from the offset to
/// the end of the slice.
///
/// If the offset is past the end of the slice, then a short read of `Ok(0)` occurs.
///
/// TODO: Test that this works.
impl ReadAt for &[u8] {
    fn read_at(&self, buf: &mut [u8], offset: u64) -> Result<usize, Self::Error> {
        // So we don't have to keep using `as usize`.
        let offset = offset as usize;

        // Can't read past the end.
        if offset >= self.len() {
            return Ok(0);
        }

        // We're sure that our read is within bounds.
        // We can either read the full requested amount or until the end.
        let amt = core::cmp::min(buf.len(), buf.len() - offset);

        // TODO: Didn't bother with mitigating copy_from_slice overheads on single byte reads.
        buf[..amt].copy_from_slice(&self[offset..offset + amt]);

        Ok(amt)
    }
}

/// WriteAt is implemented for `&mut [u8]` by copying into the slice, overwriting
/// its data.
///
/// If the number of bytes to be written exceeds the distance from the offset to the end of the
/// slice, write operations will return short writes: ultimately, `Ok(0)`; in this situation,
/// `write_all` returns an error of kind `ErrorKind::WriteZero`.
///
/// The same occurs when the offset is positioned past the end of the slice.
///
/// TODO: Figure out mutability issues
// impl WriteAt for &mut [u8] {
//     fn write_at(&self, buf: &[u8], offset: u64) -> Result<usize, Self::Error> {
//         // So we don't have to keep using `as usize`.
//         let offset = offset as usize;

//         // Can't write past the end.
//         if offset >= self.len() {
//             return Ok(0);
//         }

//         // We're sure that our write is within bounds.
//         // We can either write the full requested amount or until the end.
//         let amt = core::cmp::min(buf.len(), buf.len() - offset);

//         // TODO: Didn't bother with mitigating copy_from_slice overheads on single byte reads.
//         self[offset..offset + amt].copy_from_slice(&buf[..amt]);

//         Ok(amt)
//     }
// }

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(any(feature = "std", feature = "alloc"))))]
impl<T: ?Sized + Read> Read for alloc::boxed::Box<T> {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        T::read(self, buf)
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(any(feature = "std", feature = "alloc"))))]
impl<T: ?Sized + BufRead> BufRead for alloc::boxed::Box<T> {
    fn fill_buf(&mut self) -> Result<&[u8], Self::Error> {
        T::fill_buf(self)
    }

    fn consume(&mut self, amt: usize) {
        T::consume(self, amt)
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(any(feature = "std", feature = "alloc"))))]
impl<T: ?Sized + Write> Write for alloc::boxed::Box<T> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        T::write(self, buf)
    }

    #[inline]
    fn flush(&mut self) -> Result<(), Self::Error> {
        T::flush(self)
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(any(feature = "std", feature = "alloc"))))]
impl<T: ?Sized + Seek> Seek for alloc::boxed::Box<T> {
    #[inline]
    fn seek(&mut self, pos: crate::SeekFrom) -> Result<u64, Self::Error> {
        T::seek(self, pos)
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(any(feature = "std", feature = "alloc"))))]
impl<T: ?Sized + ReadAt> ReadAt for alloc::boxed::Box<T> {
    #[inline]
    fn read_at(&self, buf: &mut [u8], offset: u64) -> Result<usize, Self::Error> {
        T::read_at(self, buf, offset)
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(any(feature = "std", feature = "alloc"))))]
impl<T: ?Sized + WriteAt> WriteAt for alloc::boxed::Box<T> {
    #[inline]
    fn write_at(&self, buf: &[u8], offset: u64) -> Result<usize, Self::Error> {
        T::write_at(self, buf, offset)
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(any(feature = "std", feature = "alloc"))))]
impl Write for alloc::vec::Vec<u8> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        self.extend_from_slice(buf);
        Ok(buf.len())
    }

    #[inline]
    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}
