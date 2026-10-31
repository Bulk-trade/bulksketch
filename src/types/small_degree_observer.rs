//! Private observations at actual operations, independent of public progress and prices.
#![forbid(unsafe_code)]
use {crate::types::Stage, std::cell::RefCell};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum Fault {
    #[default]
    None,
    SolverMiss,
    Duplicate,
    Zero,
    Wrong,
    Incomplete,
}
#[derive(Clone, Debug, Default)]
pub(crate) struct Observation {
    pub(crate) enabled: bool,
    pub(crate) stage: Option<Stage>,
    pub(crate) factor: bool,
    pub(crate) inversions: Vec<(Stage, bool)>,
    pub(crate) residuals: Vec<(Stage, usize)>,
    pub(crate) selections: Vec<u64>,
    pub(crate) solvers: Vec<(Stage, bool)>,
    pub(crate) certificates: Vec<(bool, bool)>,
    pub(crate) fault: Fault,
    pub(crate) factor_only: bool,
}
thread_local! { static OBSERVATION: RefCell<Observation> = RefCell::new(Observation::default()); }
pub(crate) fn reset(fault: Fault, factor_only: bool) {
    OBSERVATION.with_borrow_mut(|o| {
        *o = Observation {
            enabled: true,
            fault,
            factor_only,
            ..Observation::default()
        }
    });
}
pub(crate) fn snapshot() -> Observation {
    OBSERVATION.with_borrow(Clone::clone)
}
pub(crate) fn finish() -> Observation {
    OBSERVATION.with_borrow_mut(std::mem::take)
}
pub(crate) fn stage(stage: Stage, factor: bool) {
    OBSERVATION.with_borrow_mut(|o| {
        if o.enabled {
            o.stage = Some(stage);
            o.factor = factor;
        }
    });
}
pub(crate) fn inverse() {
    OBSERVATION.with_borrow_mut(|o| {
        if o.enabled
            && let Some(stage) = o.stage
        {
            o.inversions.push((stage, o.factor));
        }
    });
}
pub(crate) fn residual(index: usize) {
    OBSERVATION.with_borrow_mut(|o| {
        if o.enabled {
            o.residuals.push((o.stage.expect("guard stage"), index));
        }
    });
}
pub(crate) fn selected(root: u64) {
    OBSERVATION.with_borrow_mut(|o| {
        if o.enabled {
            o.selections.push(root);
        }
    });
}
pub(crate) fn certificate(valid: bool) {
    OBSERVATION.with_borrow_mut(|o| {
        if o.enabled {
            o.certificates.push((o.factor, valid));
        }
    });
}
pub(crate) fn returned(roots: &mut [u64], degree: usize) -> Option<usize> {
    OBSERVATION.with_borrow_mut(|o| {
        if !o.enabled {
            return Some(degree);
        }
        o.solvers.push((o.stage.expect("solver stage"), o.factor));
        if o.factor_only && !o.factor {
            return Some(degree);
        }
        let fault = std::mem::take(&mut o.fault);
        match fault {
            Fault::None => {}
            Fault::SolverMiss => return None,
            Fault::Duplicate => roots[1] = roots[0],
            Fault::Zero => roots[0] = 0,
            Fault::Wrong => {
                for root in roots.iter_mut().take(degree) {
                    *root ^= 0x8000_0000_0000_0000;
                }
            }
            Fault::Incomplete => return Some(degree - 1),
        }
        Some(degree)
    })
}
