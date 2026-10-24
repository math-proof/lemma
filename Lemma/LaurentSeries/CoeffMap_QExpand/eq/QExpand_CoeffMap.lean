import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_LaurentCoeff
import Lemma.Definitions.Def_ModularCurve_X0
import Lemma.Int.P2MUtil

open ModularCurve IntermediateField HahnSeries

/--
[ModularCurve_coeffMap_qExpand](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_coeffMap_qExpand.lean)
-/
@[path]
private lemma main
  {R S : Type*} [CommRing R] [CommRing S]
  {f : R →+* S}
  {n : ℕ} [NeZero n]
  {x : LaurentSeries R} :
-- imply
  ModularCurve.coeffMap f (ModularCurve.qExpand R n x) = ModularCurve.qExpand S n (ModularCurve.coeffMap f x) := by
-- proof
  ext k
  by_cases hk : (n : ℤ) ∣ k
  ·
    obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]


-- created on 2026-10-23
