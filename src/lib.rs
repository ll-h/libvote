use std::iter::{Take, Skip};
use std::borrow::Borrow;
use std::ops::AddAssign;

use thiserror::Error;

pub trait Ballot {
    type Candidate;
}

impl<T> Ballot for Vec<T> {
    type Candidate = T;
}

#[derive(Debug, PartialEq, Error)]
pub enum BallotError {
    #[error("Too much candidates in this ballot")]
    InputTooLarge,
    #[error("The candidate of index {0} does not exist")]
    InvalidCandidate(usize),
    #[error("The candidate of index {0} appeared more than twice in this ballot")]
    CandidateAppearedTooMuch(usize)
}

pub trait BallotBox {
    type Proof;
    fn add_ballot<B: Ballot + Borrow<[usize]>>(&mut self, ballot: &B) -> Result<Self::Proof, BallotError>;
}

#[derive(Clone)]
pub struct CandidateIndex(usize);

pub trait HasCandidates {
    fn nb_candidates(&self) -> usize;
}

pub trait CandidateValidator : HasCandidates {
    fn validate_candidate_index(&self, unchecked_candidate_idx: usize)
        -> Result<CandidateIndex, BallotError>;
}

impl<T: HasCandidates> CandidateValidator for T {
    fn validate_candidate_index(&self, unchecked_candidate_idx: usize)
        -> Result<CandidateIndex, BallotError>
    {
        if self.nb_candidates() > unchecked_candidate_idx {
            Ok(CandidateIndex(unchecked_candidate_idx))
        }
        else {
            Err(BallotError::InvalidCandidate(unchecked_candidate_idx))
        }
    }
}

pub trait BallotValidator : HasCandidates {
    fn validate_ballot_size(&self, unchecked_ballot: &[usize])
        -> Result<(), BallotError>;
}

impl<T: HasCandidates> BallotValidator for T where
{
    fn validate_ballot_size(&self, unchecked_ballot: &[usize])
        -> Result<(), BallotError>
    {
        if unchecked_ballot.len() <= self.nb_candidates().into() {
            Ok(())
        }
        else {
            Err(BallotError::InputTooLarge)
        }
    }
}

pub trait PreferenceMatrix : CandidateValidator {
    type OpponentCounter;
    type OpponentCounterIter<'a> : Iterator<Item = &'a mut Self::OpponentCounter> where Self::OpponentCounter: 'a, Self: 'a;

    /// Returns an iterator over the counters of times a given candidate has been preferred over every of its opponents
    fn get_opponents_vote_counter_iter<'a>(&'a mut self, candidate_idx: CandidateIndex)
        -> Self::OpponentCounterIter<'a>;

    fn times_left_is_preferred_over_right(&self, left: &CandidateIndex, right: &CandidateIndex) -> &Self::OpponentCounter;
}

/// This type is meant to test the genericity of the trait PreferenceMatrix.
/// Use ContiguousAccumulatingBallotBox for better performance.
pub struct SimpleAccumulatingBallotBox<N> (Vec<Vec<N>>);

impl<N> HasCandidates for SimpleAccumulatingBallotBox<N> {
    fn nb_candidates(&self) -> usize {
        self.0.len()
    }
}

impl<N> SimpleAccumulatingBallotBox<N> {
    pub fn new(nb_candidates: usize) -> Self where
        N: Copy,
        u8: Into<N>
    {
        let mut ret = vec![vec![0.into(); nb_candidates] ; nb_candidates];
        ret.shrink_to_fit();
        for col in ret.iter_mut() {
            col.shrink_to_fit();
        }
        return Self(ret);
    }
}

/// This trait has been created so that implementors may use atomic types.
pub trait Incrementable {
    fn increment(&mut self);
}

impl<T: AddAssign + From<u8>> Incrementable for T {
    fn increment(&mut self) {
        *self += T::from(1);
    }
}

impl<N> PreferenceMatrix for SimpleAccumulatingBallotBox<N> {
    type OpponentCounter = N;
    type OpponentCounterIter<'a> = core::slice::IterMut<'a, Self::OpponentCounter> where Self::OpponentCounter: 'a;

    fn get_opponents_vote_counter_iter<'a>(&'a mut self, candidate_idx: CandidateIndex)
        -> Self::OpponentCounterIter<'a>
    {
        let usize_cidx: usize = candidate_idx.0.into();
        unsafe {
            self.0.get_unchecked_mut(usize_cidx).iter_mut()
        }
    }

    fn times_left_is_preferred_over_right(&self, left: &CandidateIndex, right: &CandidateIndex) -> &Self::OpponentCounter {
        unsafe {
            self.0.get_unchecked(left.0).get_unchecked(right.0).clone()
        }
    }
}

pub struct ContiguousAccumulatingBallotBox<N> {
    nb_candidates: usize,
    counts: Box<[N]>
}

impl<N> HasCandidates for ContiguousAccumulatingBallotBox<N> {
    fn nb_candidates(&self) -> usize {
        self.nb_candidates
    }
}

impl<N> ContiguousAccumulatingBallotBox<N> {
    pub fn new(nb_candidates: usize) -> Self where N: Default + Clone {
        let counts = vec![N::default(); nb_candidates * nb_candidates].into_boxed_slice();
        return Self{nb_candidates, counts};
    }
}

impl<N> PreferenceMatrix for ContiguousAccumulatingBallotBox<N> {
    type OpponentCounter = N;
    type OpponentCounterIter<'a> = Take<Skip<core::slice::IterMut<'a, Self::OpponentCounter>>> where Self::OpponentCounter: 'a;
    fn get_opponents_vote_counter_iter<'a>(&'a mut self, candidate_idx: CandidateIndex)
        -> Self::OpponentCounterIter<'a>
    {
        self.counts
            .iter_mut()
            .skip(self.nb_candidates * candidate_idx.0)
            .take(self.nb_candidates)
    }

    fn times_left_is_preferred_over_right(&self, left: &CandidateIndex, right: &CandidateIndex) -> &Self::OpponentCounter {
        unsafe {
            self.counts.get_unchecked(left.0 * self.nb_candidates + right.0)
        }
    }
}


impl<C> Ballot for &[C] {
    type Candidate = C;
}

impl<T> BallotBox for T where
    T: PreferenceMatrix,
    <T as PreferenceMatrix>::OpponentCounter: Incrementable
{
    type Proof = ();

    fn add_ballot<B: Ballot + Borrow<[usize]>>(&mut self, ballot : &B) -> Result<Self::Proof, BallotError>
    {
        self.validate_ballot_size(ballot.borrow())?;
        // checking that candidates are there only once
        let mut usage = [false].repeat(self.nb_candidates()); // (*)
        for candidate in ballot.borrow() {
            let candidate_idx = self.validate_candidate_index(candidate.clone())?; // (**)
            unsafe {
                let already_used = usage.get_unchecked_mut(candidate_idx.clone().0); // made safe by (*) and (**)
                if *already_used {
                    return Err(BallotError::CandidateAppearedTooMuch(candidate.clone()));
                }
                else {
                    *already_used = true;
                }
            }

            self.get_opponents_vote_counter_iter(candidate_idx)
                .zip(usage.iter())
                .for_each(|(nb_time_preferred_over_other_candidate, other_candidate_is_preferred_over_current)| {
                    if !other_candidate_is_preferred_over_current {
                        nb_time_preferred_over_other_candidate.increment();
                    }
                })
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn add_ballots<BB: BallotBox>(ballots: Vec<Vec<u8>>, bb: &mut BB) -> Result<(), BallotError>
    {
        for ballot in ballots.iter() {
            let ballot = ballot.iter().map(|c| c.clone().into()).collect::<Vec<usize>>();
            bb.add_ballot(&ballot)?;
        }
        Ok(())
    }

    trait FromNbCandidates {
        fn from_nb_candidates(nb: usize) -> Self;
    }

    impl<T: From<u8> + Copy + Default> FromNbCandidates for ContiguousAccumulatingBallotBox<T> {
        fn from_nb_candidates(nb: usize) -> Self { Self::new(nb) }
    }
    impl<T: From<u8> + Copy> FromNbCandidates for SimpleAccumulatingBallotBox<T> {
        fn from_nb_candidates(nb: usize) -> Self { Self::new(nb) }
    }

    fn make_ballot_box_with<'a, BB>(ballots: Vec<Vec<u8>>) -> Result<BB, BallotError>
        where BB: BallotBox + FromNbCandidates
    {
        let nb_candidates = ballots.iter().map(|s| s.len()).max().unwrap();
        let mut acc = BB::from_nb_candidates(nb_candidates);
        add_ballots(ballots, &mut acc)?;
        Ok(acc)
    }

    fn print_ballots(bb :&SimpleAccumulatingBallotBox<usize>) {
        for opponents in &bb.0 {
            print!("[");
            let mut opponent_it = opponents.iter();
            if let Some(opponent) = opponent_it.next() {
                print!("{}", opponent);
            }
            for opponent in opponent_it {
                print!(", {}", opponent);
            }
            println!("]");
        }
    }

    fn test_matrix<M>(ballot_box: &mut M) where M: PreferenceMatrix<OpponentCounter = usize> {
        let a = ballot_box.validate_candidate_index(0).unwrap();
        let b = ballot_box.validate_candidate_index(1).unwrap();
        let c = ballot_box.validate_candidate_index(2).unwrap();
        let alice = &a;
        let bob = &b;
        let charlie = &c;

        let mut get_opponents = |cand: &CandidateIndex| {
            ballot_box
                .get_opponents_vote_counter_iter(cand.clone())
                .map(|mut_nb| mut_nb.clone())
                .collect::<Vec<usize>>()
        };

        assert_eq!(vec![0,3,4], get_opponents(alice));
        assert_eq!(vec![1,0,3], get_opponents(bob));
        assert_eq!(vec![0,1,0], get_opponents(charlie));

        assert_eq!(&3, ballot_box.times_left_is_preferred_over_right(alice, bob));
        assert_eq!(&4, ballot_box.times_left_is_preferred_over_right(alice, charlie));
        assert_eq!(&1, ballot_box.times_left_is_preferred_over_right(bob, alice));
        assert_eq!(&3, ballot_box.times_left_is_preferred_over_right(bob, charlie));
        assert_eq!(&0, ballot_box.times_left_is_preferred_over_right(charlie, alice));
        assert_eq!(&1, ballot_box.times_left_is_preferred_over_right(charlie, bob));
    }


    #[test]
    fn test_acc_box_matrix() {
        let mut ballot_box: SimpleAccumulatingBallotBox<usize> = make_ballot_box_with(vec![
            vec![0u8,1,2],
            vec![0,2,1],
            vec![0,1],
            vec![1,0,2],
        ]).unwrap();
        print_ballots(&ballot_box);

        assert_eq!(ballot_box.0, vec![
            vec![0,3,4],
            vec![1,0,3],
            vec![0,1,0],
        ]);

        test_matrix(&mut ballot_box);
    }

    #[test]
    fn test_contiguous_acc_pref_matrix() {
        let mut ballot_box: ContiguousAccumulatingBallotBox<usize> = ContiguousAccumulatingBallotBox { 
            nb_candidates: 3,
            counts: Box::new([0usize,3,4, 1,0,3, 0,1,0]) as Box<[usize]>
        };
        
        test_matrix(&mut ballot_box);
    }

    #[test]
    fn test_contiguous_acc_box() {
        // this uses the same hard-coded values as the ones chosen for test_acc_box_matrix() 
        let ballot_box: ContiguousAccumulatingBallotBox<usize> = make_ballot_box_with(vec![
            vec![1,0,2],
            vec![0,2,1],
            vec![0,1],
            vec![0,1,2],
        ]).unwrap();

        assert_eq!(ballot_box.counts.as_ref(), &[
            0usize,3,4,
            1,0,3,
            0,1,0,
        ]);
    }

    #[test]
    fn test_acc_box_invalid_candidate() {
        let mut ballot_box = SimpleAccumulatingBallotBox::<usize>::new(3);
        let ballot = vec![0,1,4];
        assert_eq!(ballot_box.add_ballot(&ballot), Err(BallotError::InvalidCandidate(4)));
    }

    #[test]
    fn test_acc_box_overused_candidate() {
        let mut ballot_box = SimpleAccumulatingBallotBox::<usize>::new(3);
        let ballot = vec![1,2,1];
        assert_eq!(ballot_box.add_ballot(&ballot), Err(BallotError::CandidateAppearedTooMuch(1)));
    }

    #[test]
    fn test_acc_box_too_large_ballot() {
        let mut ballot_box = SimpleAccumulatingBallotBox::<usize>::new(3);
        let ballot = vec![0,1,2,3];
        assert_eq!(ballot_box.add_ballot(&ballot), Err(BallotError::InputTooLarge));
    }
}
