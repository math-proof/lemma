import Lemma.Set.CupIn_Ico.eq.Cup_UfnSub
import Lemma.Set.Cup_Ioc.eq.IocNeg_0
import Lemma.Int.AddSubNeg.eq.Neg
import Lemma.Int.SubNeg
import Lemma.Set.CupIco.eq.CupAnd
import Lemma.Set.CupRange.eq.CupIco
import Lemma.Int.EqToNat.of.Ge_0
import Lemma.Set.EqCupS.of.All_Eq
import Lemma.Int.CoeCoe.eq.Coe
open Set Int


@[main]
private lemma main
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
-- given
  (n : ℕ) :
-- imply
  ⋃ k ∈ Ico (-n : ℤ) (0 : ℤ), Ioc (k : R) (k + 1 : R) = Ioc (-n : R) (0 : R) := by
-- proof
  rw [CupIn_Ico.eq.Cup_UfnSub (-1)]
  simp [AddSubNeg.eq.Neg]
  simp [SubNeg.comm]
  rw [CupAnd.eq.CupIco]
  have h := Cup_Ioc.eq.IocNeg_0 n (R := R)
  rw [CupRange.eq.CupIco] at h
  have h_all : ∀ k ∈ Ico (0 : ℤ) (n : ℤ), Ioc (-(k : R) - 1) (-(k : R)) = Ioc (-(k.toNat : R) - 1) (-(k.toNat : R)) := by
    intro k hk
    rw [Coe.eq.CoeCoe]
    rw [EqToNat.of.Ge_0 hk.1]
  have h_union := EqCupS.of.All_Eq.set h_all
  aesop


-- created on 2025-09-29
-- updated on 2025-09-30
