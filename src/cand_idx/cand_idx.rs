#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct CandidateIndex(usize);

impl CandidateIndex {
    pub unsafe fn new(unchecked_candidate_idx: usize) -> Self {
        CandidateIndex(unchecked_candidate_idx)
    }
}

impl From<CandidateIndex> for usize {
    fn from(value: CandidateIndex) -> Self {
        value.0
    }
}

pub trait HasCandidates {
    fn nb_candidates(&self) -> usize;
}

pub trait CandidateValidator : HasCandidates {
    fn validate_candidate_index(&self, unchecked_candidate_idx: usize)
        -> Result<CandidateIndex, ()>;
}

impl<T: HasCandidates> CandidateValidator for T {
    fn validate_candidate_index(&self, unchecked_candidate_idx: usize)
        -> Result<CandidateIndex, ()>
    {
        (self.nb_candidates() > unchecked_candidate_idx)
            .then_some(CandidateIndex(unchecked_candidate_idx))
            .ok_or(())
    }
}