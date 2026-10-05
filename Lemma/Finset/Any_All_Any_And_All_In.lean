import Mathlib
import sympy.Basic

open scoped nonZeroDivisors

/--
[ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd.lean)
-/
@[main]
private lemma main
  [CommRing R] [IsDedekindDomain R] [Finite (ClassGroup R)] :
-- imply
  ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum R), ∀ c : ClassGroup R, ∃ I : (Ideal R)⁰,
      ClassGroup.mk0 I = c ∧ ∀ v : IsDedekindDomain.HeightOneSpectrum R, v.asIdeal ∣ (I : Ideal R) → v ∈ S := by
-- proof
  classical
  choose I hI using (ClassGroup.mk0_surjective (R := R))
  have hfin : (⋃ c : ClassGroup R, {v : IsDedekindDomain.HeightOneSpectrum R | v.asIdeal ∣ (I c : Ideal R)}).Finite :=
    Set.finite_iUnion fun c => Ideal.finite_factors (nonZeroDivisors.coe_ne_zero (I c))
  refine ⟨hfin.toFinset, fun c => ⟨I c, hI c, fun v hv => ?_⟩⟩
  rw [Set.Finite.mem_toFinset]
  exact Set.mem_iUnion.2 ⟨c, hv⟩


-- created on 2026-10-05
