use std::{cmp::Ordering, ops::Sub};

use crate::cand_idx::CandidateIndex;

#[derive(Clone, Debug)]
pub struct CandidatePair<N> {
    winner: CandidateIndex,
    opponent: CandidateIndex,
    winners_votes: N,
    opponents_votes: N,
}

impl<N> CandidatePair<N> {
    pub fn new(
        candidate_a: CandidateIndex,
        candidate_b: CandidateIndex,
        a_over_b_votes: N,
        b_over_a_votes: N,
    ) -> Self where N: PartialOrd {
        let mut pair = Self {
            winner: candidate_a,
            opponent: candidate_b,
            winners_votes: a_over_b_votes,
            opponents_votes: b_over_a_votes,
        };

        if pair.winners_votes < pair.opponents_votes {
            std::mem::swap(&mut pair.winner, &mut pair.opponent);
            std::mem::swap(&mut pair.winners_votes, &mut pair.opponents_votes);
        }

        pair
    }

    pub fn winner(&self) -> &CandidateIndex {
        &self.winner
    }

    pub fn opponent(&self) -> &CandidateIndex {
        &self.opponent
    }
}

impl<N: PartialEq> PartialEq for CandidatePair<N> {
    fn eq(&self, other: &Self) -> bool {
        self.winners_votes == other.winners_votes &&
        self.opponents_votes == other.opponents_votes
    }
}
impl<N: Eq> Eq for CandidatePair<N> {}


fn diff<N>(p: &CandidatePair<N>) -> N
where
    for<'a> &'a N: Sub,
    for<'a> <&'a N as Sub>::Output: Into<N>,
    N: Ord,
{
    (&p.winners_votes - &p.opponents_votes).into()
}

impl<N> Ord for CandidatePair<N> where
    for<'a> &'a N: Sub,
    for<'a> <&'a N as Sub>::Output: Into<N>,
    N: Ord,
{
    /// Ordered by those criteria:
    /// 1. Biggest vote difference first
    /// 2. Fewest opponent's votes
    /// 3. Highest winner's votes
    fn cmp(&self, other: &Self) -> Ordering {
        // higher diff first, so the order is other.cmp(self)
        diff(&other).cmp(&diff(&self))
            .then_with(|| self.opponents_votes.cmp(&other.opponents_votes))
            .then_with(|| self.winners_votes.cmp(&self.winners_votes))
    }
}

impl<N> PartialOrd for CandidatePair<N> where
    N: Ord,
    for<'a> &'a N: Sub,
    for<'a> <&'a N as Sub>::Output: Into<N>,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}


#[cfg(test)]
mod tests {
    use crate::cand_idx::CandidateIndex;

    use super::*;

    #[test]
    fn test_new() {
        // create two candidates
        let c1 = unsafe{CandidateIndex::new(0)};
        let c2 = unsafe{CandidateIndex::new(1)};

        // create a pair with c1 having more votes than c2
        let p1 = CandidatePair::new(c1, c2, 10, 5);

        // check that the winner and opponent are correct
        assert_eq!(p1.winner, c1);
        assert_eq!(p1.opponent, c2);

        // check that the votes are correct
        assert_eq!(p1.winners_votes, 10);
        assert_eq!(p1.opponents_votes, 5);

        // create another pair with c2 having more votes than c1
        let p2 = CandidatePair::new(c1, c2, 3, 7);

        // check that the winner and opponent are swapped
        assert_eq!(p2.winner, c2);
        assert_eq!(p2.opponent, c1);

        // check that the votes are swapped
        assert_eq!(p2.winners_votes, 7);
        assert_eq!(p2.opponents_votes, 3);
    }

    #[test]
    fn integ() {
        let alice   = unsafe{CandidateIndex::new(0)};
        let bernard = unsafe{CandidateIndex::new(1)};
        let charles = unsafe{CandidateIndex::new(2)};

        let pa = CandidatePair{
            winner: alice.clone(),
            opponent: bernard.clone(),
            winners_votes: 70,
            opponents_votes: 30
        };
        let pb = CandidatePair{
            winner: charles.clone(),
            opponent: bernard.clone(),
            winners_votes: 20,
            opponents_votes: 30
        };

        assert_ne!(&pa, &pb);
        let mut pairs = vec![pa, pb];

        pairs.sort_unstable();

        assert_eq!(alice, pairs.iter().next().unwrap().winner.into());
    }
}