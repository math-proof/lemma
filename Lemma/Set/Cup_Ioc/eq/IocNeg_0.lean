import sympy.sets.sets
import Lemma.Set.Cup.eq.UnionCupS
import Lemma.Set.SDiff_Singleton.eq.Range
import Lemma.Set.InterRange.eq.Singleton
import Lemma.Set.CupIn_Singleton.eq.Ufn
import Lemma.Set.UnionIocS.eq.Ioc.of.Le.Le
import Lemma.Algebra.CoeAdd.eq.AddCoeS
import Lemma.Algebra.NegAdd.eq.SubNeg
open Set Algebra


@[main]
private lemma main
  [LinearOrderedRing R]
-- given
  (n : ℕ) :
-- imply
  ⋃ k ∈ range n, Ioc (-k - 1 : R) (-k : R) = Ioc (-n : R) (0 : R) := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Cup.eq.UnionCupS.fin (B := {n})]
    rw [SDiff_Singleton.eq.Range]
    rw [InterRange.eq.Singleton]
    simp only [CupIn_Singleton.eq.Ufn.fin]
    rw [ih]
    rw [UnionIocS.eq.Ioc.of.Le.Le]
    ·
      rw [CoeAdd.eq.AddCoeS.nat]
      rw [NegAdd.eq.SubNeg]
      norm_num
    repeat simp


-- created on 2025-08-05
-- updated on 2025-08-14
