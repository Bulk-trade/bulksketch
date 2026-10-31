//! Complete-operation dispatch; arithmetic stays statically monomorphized.
#![forbid(unsafe_code)]

#[cfg(target_arch = "x86_64")]
use crate::backend::{x86_pclmul::Pclmul, x86_vpclmul512::Vpclmul512};
use {
    super::{scratch::InsertScratch, shape::SketchShape},
    crate::{
        backend::{contract::BulkKernels, detect, portable::Portable},
        decode::{
            probe::Probe,
            row::{RowBudget, RowDecoder, RowExecution, RowInput, RowProgress, RowResult},
            scratch::RowWorkspace,
            stages::{BinaryDecoder, Execution},
        },
        field::BinaryField,
        types::{BackendError, BackendId, BackendRequest, DecodeError, Stage, WorkMeter},
    },
};

/// Checked whole-operation decode selection, independent of frozen state and wire bytes.
#[derive(Clone, Copy)]
pub struct Decoder<F: BinaryField> {
    begin: fn(RowBudget, u64) -> DecodeExecution<F>,
    backend: BackendId,
    splitter_seed: u64,
    pub(super) difference: fn(&mut [u64], &[u64], &[u8]) -> bool,
    #[cfg(test)]
    pub(super) skip_shortcuts: bool,
}

impl<F: BinaryField> std::fmt::Debug for Decoder<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // The caller's seed is secret, including its derived basis.
        f.debug_struct("Decoder").finish_non_exhaustive()
    }
}

impl<F: BinaryField> Decoder<F> {
    /// Resolve a built backend once; forced requests retain all availability checks.
    ///
    /// The caller supplies the splitter seed; the core draws no randomness. GF64
    /// maps zero to one and leaves every other seed unchanged. For a uniform seed,
    /// only one has two preimages; its total variation from uniform nonzero is
    /// less than 2^-64. Scaling the polynomial basis by this nonzero word preserves
    /// completeness. Use a secret seed in production and a fixed seed in simulations.
    ///
    /// # Errors
    /// The requested backend is unavailable in this build or on this CPU/OS.
    pub fn new(backend: BackendRequest, splitter_seed: u64) -> Result<Self, BackendError> {
        let selected = detect::resolve(backend)?;
        let begin = match selected {
            BackendId::Portable => |budget, seed| {
                let mut row = <BinaryDecoder as RowDecoder<F, Portable>>::begin(budget);
                row.set_splitter_seed(seed);
                DecodeExecution::Portable(row)
            },
            #[cfg(target_arch = "x86_64")]
            BackendId::Pclmul => |budget, seed| {
                let mut row = <BinaryDecoder as RowDecoder<F, Pclmul>>::begin(budget);
                row.set_splitter_seed(seed);
                DecodeExecution::Pclmul(row)
            },
            #[cfg(target_arch = "x86_64")]
            BackendId::Vpclmul512 => |budget, seed| {
                let mut row = <BinaryDecoder as RowDecoder<F, Vpclmul512>>::begin(budget);
                row.set_splitter_seed(seed);
                DecodeExecution::Vpclmul512(row)
            },
            _ => unreachable!("backend must be resolved before dispatch"),
        };
        let difference: Difference = match selected {
            BackendId::Portable => <Portable as BulkKernels<F>>::difference,
            #[cfg(target_arch = "x86_64")]
            BackendId::Pclmul => <Pclmul as BulkKernels<F>>::difference,
            #[cfg(target_arch = "x86_64")]
            BackendId::Vpclmul512 => <Vpclmul512 as BulkKernels<F>>::difference,
            _ => unreachable!("resolved backend"),
        };
        Ok(Self {
            backend: selected,
            begin,
            splitter_seed,
            difference,
            #[cfg(test)]
            skip_shortcuts: false,
        })
    }

    pub(super) fn begin_probe(
        &self,
        budget: RowBudget,
        difference: &[u64],
    ) -> Option<DecodeExecution<F>> {
        Probe::new(budget, difference).map(|probe| DecodeExecution::Probe(probe, self.backend))
    }

    pub(super) fn begin(self, budget: RowBudget) -> DecodeExecution<F> {
        (self.begin)(budget, self.splitter_seed)
    }

    #[inline(always)]
    pub(super) fn restart(&self, execution: &mut DecodeExecution<F>, budget: RowBudget) {
        // A request retains its selected decoder, so the existing variant stays valid.
        match execution {
            DecodeExecution::Probe(..) => *execution = self.begin(budget),
            DecodeExecution::Portable(row) => row.restart(budget, self.splitter_seed),
            #[cfg(target_arch = "x86_64")]
            DecodeExecution::Pclmul(row) => row.restart(budget, self.splitter_seed),
            #[cfg(target_arch = "x86_64")]
            DecodeExecution::Vpclmul512(row) => row.restart(budget, self.splitter_seed),
        }
    }
}

type Difference = fn(&mut [u64], &[u64], &[u8]) -> bool;

#[derive(Debug)]
pub(super) enum DecodeExecution<F: BinaryField> {
    Probe(Probe, BackendId),
    Portable(Execution<F, Portable>),
    #[cfg(target_arch = "x86_64")]
    Pclmul(Execution<F, Pclmul>),
    #[cfg(target_arch = "x86_64")]
    Vpclmul512(Execution<F, Vpclmul512>),
}

impl<F: BinaryField> DecodeExecution<F> {
    pub(super) fn enable_v3(&mut self) {
        match self {
            Self::Probe(..) => {}
            Self::Portable(row) => row.enable_v3(),
            #[cfg(target_arch = "x86_64")]
            Self::Pclmul(row) => row.enable_v3(),
            #[cfg(target_arch = "x86_64")]
            Self::Vpclmul512(row) => row.enable_v3(),
        }
    }

    pub(super) fn start_degrees(&mut self, capacity: usize) {
        match self {
            Self::Probe(..) => {}
            Self::Portable(row) => row.start_degrees(capacity),
            #[cfg(target_arch = "x86_64")]
            Self::Pclmul(row) => row.start_degrees(capacity),
            #[cfg(target_arch = "x86_64")]
            Self::Vpclmul512(row) => row.start_degrees(capacity),
        }
    }
    pub(super) fn verification_count(&self) -> usize {
        match self {
            Self::Probe(probe, _) => probe.count(),
            Self::Portable(row) => row.verification_count(),
            #[cfg(target_arch = "x86_64")]
            Self::Pclmul(row) => row.verification_count(),
            #[cfg(target_arch = "x86_64")]
            Self::Vpclmul512(row) => row.verification_count(),
        }
    }
    pub(super) fn reject_upper(&mut self, capacity: usize) {
        match self {
            Self::Probe(probe, _) => probe.reject(capacity),
            Self::Portable(row) => row.reject_upper(capacity),
            #[cfg(target_arch = "x86_64")]
            Self::Pclmul(row) => row.reject_upper(capacity),
            #[cfg(target_arch = "x86_64")]
            Self::Vpclmul512(row) => row.reject_upper(capacity),
        }
    }

    pub(super) fn completed_result<'w>(
        &self,
        workspace: &'w RowWorkspace<'_>,
    ) -> Result<RowResult<'w>, DecodeError> {
        match self {
            Self::Probe(probe, _) => {
                assert!(probe.next_stage().is_none(), "drained probe");
                Ok(RowResult::Decoded(&workspace.roots[..probe.count()]))
            }
            Self::Portable(row) => row.completed_result(workspace),
            #[cfg(target_arch = "x86_64")]
            Self::Pclmul(row) => row.completed_result(workspace),
            #[cfg(target_arch = "x86_64")]
            Self::Vpclmul512(row) => row.completed_result(workspace),
        }
    }

    pub(super) fn next_stage(&self) -> Option<Stage> {
        match self {
            Self::Probe(probe, _) => probe.next_stage(),
            Self::Portable(row) => row.next_stage(),
            #[cfg(target_arch = "x86_64")]
            Self::Pclmul(row) => row.next_stage(),
            #[cfg(target_arch = "x86_64")]
            Self::Vpclmul512(row) => row.next_stage(),
        }
    }

    pub(super) fn run_next(
        &mut self,
        input: RowInput<'_>,
        workspace: &mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<RowProgress, DecodeError> {
        match self {
            Self::Probe(probe, backend) => run_probe::<F>(
                *backend,
                probe,
                input.difference,
                workspace.verification,
                workspace.roots,
                meter,
            ),
            Self::Portable(row) => row.run_next(input, workspace, meter),
            #[cfg(target_arch = "x86_64")]
            Self::Pclmul(row) => row.run_next(input, workspace, meter),
            #[cfg(target_arch = "x86_64")]
            Self::Vpclmul512(row) => row.run_next(input, workspace, meter),
        }
    }
}

#[inline(always)]
pub(super) fn run_probe<F: BinaryField>(
    backend: BackendId,
    probe: &mut Probe,
    difference: &[u64],
    verification: &mut [u64],
    roots: &mut [u64],
    meter: &mut WorkMeter,
) -> Result<RowProgress, DecodeError> {
    match backend {
        BackendId::Portable => {
            probe.run_next::<F, Portable>(difference, verification, roots, meter)
        }
        #[cfg(target_arch = "x86_64")]
        BackendId::Pclmul => probe.run_next::<F, Pclmul>(difference, verification, roots, meter),
        #[cfg(target_arch = "x86_64")]
        BackendId::Vpclmul512 => {
            probe.run_next::<F, Vpclmul512>(difference, verification, roots, meter)
        }
        _ => unreachable!("resolved probe backend"),
    }
}

type Toggle<F> = fn(&SketchShape<F>, &mut [u64], &mut [u64], u64);
type Batch<F> = fn(&SketchShape<F>, &mut [u64], &mut [u64], &[u64], &mut InsertScratch);
type Xor = fn(&mut [u64], &[u64]);

#[cfg(all(test, target_arch = "x86_64"))]
mod portable_tests;

#[derive(Clone, Copy, Debug)]
pub(crate) struct InsertDispatch<F: BinaryField> {
    pub(crate) toggle: Toggle<F>,
    pub(crate) batch: Batch<F>,
    pub(crate) xor: Xor,
}

impl<F: BinaryField> InsertDispatch<F> {
    pub(crate) fn new(backend: BackendId) -> Self {
        match backend {
            BackendId::Portable => Self {
                toggle: toggle::<F, Portable>,
                batch: batch::<F, Portable>,
                xor: <Portable as BulkKernels<F>>::xor_assign,
            },
            #[cfg(target_arch = "x86_64")]
            BackendId::Pclmul => Self {
                toggle: toggle::<F, Pclmul>,
                batch: batch::<F, Pclmul>,
                xor: <Pclmul as BulkKernels<F>>::xor_assign,
            },
            #[cfg(target_arch = "x86_64")]
            BackendId::Vpclmul512 => Self {
                toggle: toggle::<F, Vpclmul512>,
                batch: batch::<F, Vpclmul512>,
                xor: <Vpclmul512 as BulkKernels<F>>::xor_assign,
            },
            _ => unreachable!("backend must be resolved before dispatch"),
        }
    }
}

fn toggle<F: BinaryField, K: BulkKernels<F>>(
    shape: &SketchShape<F>,
    words: &mut [u64],
    zero: &mut [u64],
    id: u64,
) {
    if id == 0 {
        zero[0] ^= 1;
        return;
    }
    // A one-bucket sketch (one per bucket in a per-row layout): its entire word slice is
    // already the destination row, so no modulo or prefix scan is necessary.
    if shape.bucket_count() == 1 {
        K::insert_nonzero(words, &[id]);
        return;
    }
    let bucket = shape.bucket_for(id);
    let offset: usize = shape.capacities()[..bucket]
        .iter()
        .map(|&c| usize::from(c))
        .sum();
    let capacity = usize::from(shape.capacities()[bucket]);
    K::insert_nonzero(&mut words[offset..offset + capacity], &[id]);
}

fn batch<F: BinaryField, K: BulkKernels<F>>(
    shape: &SketchShape<F>,
    words: &mut [u64],
    zero: &mut [u64],
    ids: &[u64],
    scratch: &mut InsertScratch,
) {
    let buckets = shape.bucket_count();
    if buckets == 1 && ids.iter().all(|&id| id != 0) {
        K::insert_nonzero(words, ids);
        return;
    }
    let offsets = &mut scratch.offsets[..=buckets];
    offsets.fill(0);
    for &id in ids {
        if id == 0 {
            zero[0] ^= 1;
        } else {
            offsets[shape.bucket_for(id) + 1] += 1;
        }
    }
    for b in 0..buckets {
        offsets[b + 1] += offsets[b];
    }
    let cursors = &mut scratch.cursors[..buckets];
    cursors.copy_from_slice(&offsets[..buckets]);
    for &id in ids {
        if id != 0 {
            let bucket = shape.bucket_for(id);
            scratch.ids[cursors[bucket]] = id;
            cursors[bucket] += 1;
        }
    }
    let mut offset = 0;
    for (bucket, &capacity) in shape.capacities().iter().enumerate() {
        let end = offset + usize::from(capacity);
        K::insert_nonzero(
            &mut words[offset..end],
            &scratch.ids[offsets[bucket]..offsets[bucket + 1]],
        );
        offset = end;
    }
}

#[cfg(all(test, target_arch = "x86_64"))]
mod auto_tests;
