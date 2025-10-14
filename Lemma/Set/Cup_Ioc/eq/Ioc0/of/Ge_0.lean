import sympy.sets.sets
import Lemma.Set.Cup_Ioc.eq.Ioc0
import Lemma.Set.CupRange.eq.CupIco
import Lemma.Int.EqToNat.of.Ge_0
import Lemma.Set.EqCupS.of.All_Eq
import Lemma.Int.CoeCoe.eq.Coe
open Set Int


@[main]
private lemma main
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  {n : ℤ}
-- given
  (h : n ≥ 0) :
-- imply
  ⋃ k ∈ Ico 0 n, Ioc (k : R) (k + 1 : R) = Ioc (0 : R) (n : R) := by
-- proof
  have h_n := Cup_Ioc.eq.Ioc0 (R := R)
  specialize h_n n.toNat
  rw [CupRange.eq.CupIco] at h_n
  rw [EqToNat.of.Ge_0 h] at h_n
  have h_all : ∀ k ∈ Ico 0 n, Ioc (k.toNat : R) (k.toNat + 1) = Ioc (k : R) (k + 1) := by
    intro k hk
    simp_all
    rw [Coe.eq.CoeCoe k.toNat]
    rw [EqToNat.of.Ge_0]
    aesop
  rw [EqCupS.of.All_Eq.set h_all] at h_n
  rw [Coe.eq.CoeCoe n.toNat] at h_n
  rwa [EqToNat.of.Ge_0 h] at h_n


-- created on 2025-10-01
