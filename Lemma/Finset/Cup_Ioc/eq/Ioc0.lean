import Lemma.Set.SDiff_Singleton.eq.Range
import Lemma.Set.InterRange.eq.Singleton
import Lemma.Set.UnionIocS.eq.Ioc.of.Le.Le
import Lemma.Set.Union
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Int.NegAdd.eq.SubNeg
import Lemma.Finset.Cup.eq.UnionCupS
import Lemma.Finset.CupIn_Singleton.eq.UFn
open Set Nat Int Finset


@[main]
private lemma main
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
-- given
  (n : ℕ) :
-- imply
  ⋃ k ∈ Finset.range n, Ioc (k : R) (k + 1 : R) = Ioc (0 : R) (n : R) := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Cup.eq.UnionCupS (B := {n})]
    rw [SDiff_Singleton.eq.Range]
    rw [InterRange.eq.Singleton]
    simp only [CupIn_Singleton.eq.UFn]
    rw [ih]
    rw [Union.comm]
    rw [UnionIocS.eq.Ioc.of.Le.Le]
    ·
      rw [CoeAdd.eq.AddCoeS]
      norm_num
    repeat simp


-- created on 2025-09-29
