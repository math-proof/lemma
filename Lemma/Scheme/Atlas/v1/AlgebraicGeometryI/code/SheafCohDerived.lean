import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.SheafCohDerived
open CohomologyP1 SheafCohomology CategoryTheory CategoryTheory.Limits SheafCohDerived


namespace SheafCohDerived

/--
[euler_chi_additive_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohDerived.lean)
-/
@[path]
lemma euler_chi_additive_step
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  ((Module.finrank k (H0 k (n + 1)) : ℤ) - (Module.finrank k (H1 k (n + 1)) : ℤ)) - ((Module.finrank k (H0 k n) : ℤ) - (Module.finrank k (H1 k n) : ℤ)) = 1 := by
-- proof
  rw [euler_characteristic k (n + 1), euler_characteristic k n]
  ring

end SheafCohDerived

/--
[serre_duality_derived](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohDerived.lean)
-/
@[path]
private lemma serre_duality_derived_eq
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  Module.finrank k (H1 k n) = Module.finrank k (H0 k (-2 - n)) := by
-- proof
  apply SheafCohDerived.serre_duality_derived k n

/--
[cech_effaceability_witness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohDerived.lean)
-/
@[path]
private lemma cech_effaceability_witness_eq
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  ∃ N : ℤ, 0 ≤ N ∧ n ≤ N ∧ Module.finrank k (H1 k N) = 0 := by
-- proof
  apply SheafCohDerived.cech_effaceability_witness k n


-- created on 2026-10-23
