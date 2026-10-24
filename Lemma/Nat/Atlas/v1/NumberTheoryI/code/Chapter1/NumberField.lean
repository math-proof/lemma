import Mathlib
import sympy.Basic
open NumberField


/--
[number_field_and_ring_of_integers](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/NumberField.lean)
-/
@[path]
lemma number_field_and_ring_of_integers
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  FiniteDimensional ℚ K ∧ (𝓞 K = ↥(integralClosure ℤ K)) :=
-- proof
  ⟨inferInstance, rfl⟩


-- created on 2026-10-23
