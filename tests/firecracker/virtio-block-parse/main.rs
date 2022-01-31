// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR MIT

// Example from Firecracker virtio block device
// We test the parse function against an arbitrary guest memory
// And check that the parse never reads the same descriptor twice

#![allow(dead_code)]
#![allow(unused_variables)]
macro_rules! error {
    ( $( $x:expr ),* ) => {};
}

struct MyError {}

unsafe impl kani::Invariant for MyError {
    fn is_valid(&self) -> bool {
        true
    }
}

#[derive(Default, Clone, Copy)]
pub struct GuestAddress(pub u64);

unsafe impl kani::Invariant for GuestAddress {
    fn is_valid(&self) -> bool {
        true
    }
}

static mut TRACK_CHECKED_OFFSET_NONE: bool = false;
static mut TRACK_READ_OBJ: Option<GuestAddress> = None;

pub struct GuestMemoryMmap {}

impl GuestMemoryMmap {
    fn checked_offset(&self, base: GuestAddress, offset: usize) -> Option<GuestAddress> {
        let mut retval = None;
        if kani::any() {
            if let Some(sum) = base.0.checked_add(offset as u64) {
                retval = Some(GuestAddress(sum))
            }
        }
        unsafe {
            if retval.is_none() && !TRACK_CHECKED_OFFSET_NONE {
                TRACK_CHECKED_OFFSET_NONE = true;
            }
        }
        return retval;
    }

    fn read_obj<T: kani::Invariant>(&self, addr: GuestAddress) -> Result<T, MyError> {
        // This assertion means that no descriptor is read more than once
        unsafe {
            if let Some(prev_addr) = TRACK_READ_OBJ {
                assert!(prev_addr.0 != addr.0);
            }
            if kani::any() && TRACK_READ_OBJ.is_none() {
                TRACK_READ_OBJ = Some(addr);
            }
        }
        if kani::any() { Ok(kani::any::<T>()) } else { Err(kani::any::<MyError>()) }
    }

    fn read_obj_request_header(&self, addr: GuestAddress) -> Result<RequestHeader, Error> {
        if kani::any() { Ok(kani::any::<RequestHeader>()) } else { Err(kani::any::<Error>()) }
    }
}

pub const VIRTQ_DESC_F_NEXT: u16 = 0x1;
pub const VIRTQ_DESC_F_WRITE: u16 = 0x2;

/// A virtio descriptor constraints with C representive.
#[repr(C)]
#[derive(Default, Clone, Copy)]
struct Descriptor {
    addr: u64,
    len: u32,
    flags: u16,
    next: u16,
}

unsafe impl kani::Invariant for Descriptor {
    fn is_valid(&self) -> bool {
        true
    }
}

/// A virtio descriptor chain.
pub struct DescriptorChain<'a> {
    desc_table: GuestAddress,
    queue_size: u16,
    ttl: u16, // used to prevent infinite chain cycles

    /// Reference to guest memory
    pub mem: &'a GuestMemoryMmap,

    /// Index into the descriptor table
    pub index: u16,

    /// Guest physical address of device specific data
    pub addr: GuestAddress,

    /// Length of device specific data
    pub len: u32,

    /// Includes next, write, and indirect bits
    pub flags: u16,

    /// Index into the descriptor table of the next descriptor if flags has
    /// the next bit set
    pub next: u16,
}

impl<'a> DescriptorChain<'a> {
    fn checked_new(
        mem: &GuestMemoryMmap,
        desc_table: GuestAddress,
        queue_size: u16,
        index: u16,
    ) -> Option<DescriptorChain> {
        if index >= queue_size {
            return None;
        }

        let desc_head = mem.checked_offset(desc_table, (index as usize) * 16)?;
        mem.checked_offset(desc_head, 16)?;

        // These reads can't fail unless Guest memory is hopelessly broken.
        let desc: Descriptor = match mem.read_obj(desc_head) {
            Ok(ret) => ret,
            Err(_) => {
                // TODO log address
                error!("Failed to read from memory");
                return None;
            }
        };
        let chain = DescriptorChain {
            mem,
            desc_table,
            queue_size,
            ttl: queue_size,
            index,
            addr: GuestAddress(desc.addr),
            len: desc.len,
            flags: desc.flags,
            next: desc.next,
        };

        if chain.is_valid() { Some(chain) } else { None }
    }

    // Kani change: add check to avoid self-loops
    fn is_valid(&self) -> bool {
        !self.has_next() || (self.next < self.queue_size && self.next != self.index)
    }

    /// Gets if this descriptor chain has another descriptor chain linked after it.
    pub fn has_next(&self) -> bool {
        self.flags & VIRTQ_DESC_F_NEXT != 0 && self.ttl > 1
    }

    /// If the driver designated this as a write only descriptor.
    ///
    /// If this is false, this descriptor is read only.
    /// Write only means the the emulated device can write and the driver can read.
    pub fn is_write_only(&self) -> bool {
        self.flags & VIRTQ_DESC_F_WRITE != 0
    }

    /// Gets the next descriptor in this descriptor chain, if there is one.
    ///
    /// Note that this is distinct from the next descriptor chain returned by `AvailIter`, which is
    /// the head of the next _available_ descriptor chain.
    pub fn next_descriptor(&self) -> Option<DescriptorChain<'a>> {
        if self.has_next() {
            DescriptorChain::checked_new(self.mem, self.desc_table, self.queue_size, self.next).map(
                |mut c| {
                    c.ttl = self.ttl - 1;
                    c
                },
            )
        } else {
            None
        }
    }
}

#[derive(Copy, Clone, Default)]
#[repr(C)]
pub struct RequestHeader {
    request_type: u32,
    _reserved: u32,
    sector: u64,
}

unsafe impl kani::Invariant for RequestHeader {
    fn is_valid(&self) -> bool {
        true
    }
}

impl RequestHeader {
    pub fn new(request_type: u32, sector: u64) -> RequestHeader {
        RequestHeader { request_type, _reserved: 0, sector }
    }
    fn read_from(memory: &GuestMemoryMmap, addr: GuestAddress) -> Result<Self, Error> {
        memory.read_obj_request_header(addr)
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum RequestType {
    In,
    Out,
    Flush,
    GetDeviceID,
    Unsupported(u32),
}

pub const VIRTIO_BLK_T_IN: u32 = 0;
pub const VIRTIO_BLK_T_OUT: u32 = 1;
pub const VIRTIO_BLK_T_FLUSH: u32 = 4;
pub const VIRTIO_BLK_T_GET_ID: u32 = 8;

impl From<u32> for RequestType {
    fn from(value: u32) -> Self {
        match value {
            VIRTIO_BLK_T_IN => RequestType::In,
            VIRTIO_BLK_T_OUT => RequestType::Out,
            VIRTIO_BLK_T_FLUSH => RequestType::Flush,
            VIRTIO_BLK_T_GET_ID => RequestType::GetDeviceID,
            t => RequestType::Unsupported(t),
        }
    }
}

#[derive(Debug)]
pub enum Error {
    /// Guest gave us too few descriptors in a descriptor chain.
    DescriptorChainTooShort,
    /// Guest gave us a descriptor that was too short to use.
    DescriptorLengthTooSmall,
    // Kani change: simplify error types
    // /// Getting a block's metadata fails for any reason.
    // GetFileMetadata(std::io::Error),
    // /// Guest gave us bad memory addresses.
    // GuestMemory(GuestMemoryError),
    /// The data length is invalid.
    InvalidDataLength,
    /// The requested operation would cause a seek beyond disk end.
    InvalidOffset,
    /// Guest gave us a read only descriptor that protocol says to write to.
    UnexpectedReadOnlyDescriptor,
    /// Guest gave us a write only descriptor that protocol says to read from.
    UnexpectedWriteOnlyDescriptor,
    // Kani change: simplify error types
    // // Error coming from the IO engine.
    // FileEngine(io::Error),
    // // Error manipulating the backing file.
    // BackingFile(std::io::Error),
    // // Error opening eventfd.
    // EventFd(std::io::Error),
    // // Error creating an irqfd.
    // IrqTrigger(std::io::Error),
    // // Error coming from the rate limiter.
    // RateLimiter(std::io::Error),
    // // Persistence error.
    // Persist(crate::virtio::persist::Error),
}

unsafe impl kani::Invariant for Error {
    fn is_valid(&self) -> bool {
        matches!(
            *self,
            Error::DescriptorChainTooShort
                | Error::DescriptorLengthTooSmall
                | Error::InvalidDataLength
                | Error::InvalidOffset
                | Error::UnexpectedReadOnlyDescriptor
                | Error::UnexpectedWriteOnlyDescriptor
        )
    }
}

pub const SECTOR_SHIFT: u8 = 9;
pub const SECTOR_SIZE: u64 = (0x01_u64) << SECTOR_SHIFT;
pub const VIRTIO_BLK_ID_BYTES: u32 = 20;

pub struct Request {
    pub r#type: RequestType,
    pub data_len: u32,
    pub status_addr: GuestAddress,
    sector: u64,
    data_addr: GuestAddress,
}

impl Request {
    pub fn parse(
        avail_desc: &DescriptorChain,
        mem: &GuestMemoryMmap,
        num_disk_sectors: u64,
    ) -> Result<Request, Error> {
        // The head contains the request type which MUST be readable.
        if avail_desc.is_write_only() {
            return Err(Error::UnexpectedWriteOnlyDescriptor);
        }

        let request_header = RequestHeader::read_from(mem, avail_desc.addr)?;
        let mut req = Request {
            r#type: RequestType::from(request_header.request_type),
            sector: request_header.sector,
            data_addr: GuestAddress(0),
            data_len: 0,
            status_addr: GuestAddress(0),
        };

        let data_desc;
        let status_desc;
        let desc = avail_desc
            .next_descriptor()
            .ok_or(Error::DescriptorChainTooShort)?;

        if !desc.has_next() {
            status_desc = desc;
            // Only flush requests are allowed to skip the data descriptor.
            if req.r#type != RequestType::Flush {
                return Err(Error::DescriptorChainTooShort);
            }
        } else {
            data_desc = desc;
            // Kani change: add chain loop check
            if data_desc.next == avail_desc.index {
                return Err(Error::DescriptorChainTooShort);
            }
            status_desc = data_desc
                .next_descriptor()
                .ok_or(Error::DescriptorChainTooShort)?;

            if data_desc.is_write_only() && req.r#type == RequestType::Out {
                return Err(Error::UnexpectedWriteOnlyDescriptor);
            }
            if !data_desc.is_write_only() && req.r#type == RequestType::In {
                return Err(Error::UnexpectedReadOnlyDescriptor);
            }
            if !data_desc.is_write_only() && req.r#type == RequestType::GetDeviceID {
                return Err(Error::UnexpectedReadOnlyDescriptor);
            }

            req.data_addr = data_desc.addr;
            req.data_len = data_desc.len;
        }

        // check request validity
        match req.r#type {
            RequestType::In | RequestType::Out => {
                // Check that the data length is a multiple of 512 as specified in the virtio standard.
                if u64::from(req.data_len) % SECTOR_SIZE != 0 {
                    return Err(Error::InvalidDataLength);
                }
                let top_sector = req
                    .sector
                    .checked_add(u64::from(req.data_len) >> SECTOR_SHIFT)
                    .ok_or(Error::InvalidOffset)?;
                if top_sector > num_disk_sectors {
                    return Err(Error::InvalidOffset);
                }
            }
            RequestType::GetDeviceID => {
                if req.data_len < VIRTIO_BLK_ID_BYTES {
                    return Err(Error::InvalidDataLength);
                }
            }
            _ => {}
        }

        // The status MUST always be writable.
        if !status_desc.is_write_only() {
            return Err(Error::UnexpectedReadOnlyDescriptor);
        }

        if status_desc.len < 1 {
            return Err(Error::DescriptorLengthTooSmall);
        }

        req.status_addr = status_desc.addr;

        Ok(req)
    }
}

fn is_nonzero_pow2(x: u16) -> bool {
    unsafe { (x != 0) && ((x & (x - 1)) == 0) }
}

fn main() {
    let mem = GuestMemoryMmap {};
    let queue_size: u16 = kani::any();
    if !is_nonzero_pow2(queue_size) {
        return;
    }
    let index: u16 = kani::any();
    let desc_table = GuestAddress(kani::any::<u64>() & 0xffff_ffff_ffff_fff0);
    let desc = DescriptorChain::checked_new(&mem, desc_table, queue_size, index);
    match desc {
        Some(x) => {
            let addr = desc_table.0 + (index as u64) * 16; //< this arithmetic cannot fail
            unsafe {
                if let Some(v) = TRACK_READ_OBJ {
                    assert!(v.0 == addr)
                }
            }
            assert!(x.index == index);
            assert!(x.index < queue_size);
            if x.has_next() {
                assert!(x.next < queue_size);
            }
            let req = Request::parse(&x, &mem, kani::any::<u64>());
            if let Ok(req) = req {
                unsafe {
                    assert!(!TRACK_CHECKED_OFFSET_NONE);
                }
            }
        }
        None => assert!(true),
    };
}
