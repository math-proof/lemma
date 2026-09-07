import Lemma.Set.SDiff_Finset.eq.Range
import Lemma.Set.InterRange.eq.Finset
import Lemma.Set.UnionIocS.eq.Ioc.of.Le.Le
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Int.NegAdd.eq.SubNeg
import Lemma.Finset.Cup.eq.UnionCupS
import Lemma.Finset.CupFinset.eq.UFn
open Set Nat Int Finset


@[main]
private lemma main
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
-- given
  (n : ℕ) :
-- imply
  ⋃ k ∈ Finset.range n, Ioc (-k - 1 : R) (-k : R) = Ioc (-n : R) (0 : R) := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Cup.eq.UnionCupS (B := {n})]
    rw [SDiff_Finset.eq.Range]
    rw [InterRange.eq.Finset]
    simp only [CupFinset.eq.UFn]
    rw [ih]
    rw [UnionIocS.eq.Ioc.of.Le.Le]
    ·
      rw [CoeAdd.eq.AddCoeS]
      rw [NegAdd.eq.SubNeg]
      norm_num
    repeat simp


-- created on 2018-10-07
-- updated on 2025-08-14
