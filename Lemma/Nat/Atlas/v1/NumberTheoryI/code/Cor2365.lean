import Mathlib
import Initialize.Tactic.Attr.Basic
open TensorProduct LinearMap in


/--
[tensor_rTensor_additive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2365.lean)
-/
@[path]
lemma tensor_rTensor_additive
  [CommRing R]
  [AddCommGroup M]
  [AddCommGroup N]
  [Module R M]
  [Module R N]
  {A : Type*}
  [AddCommGroup A]
  [Module R A] :
-- imply
  (LinearMap.rTensor A (0 : M →ₗ[R] N) = 0) ∧ (∀ (f g : M →ₗ[R] N), LinearMap.rTensor A (f + g) = LinearMap.rTensor A f + LinearMap.rTensor A g) :=
-- proof
  ⟨LinearMap.rTensor_zero A, LinearMap.rTensor_add A⟩


-- created on 2026-10-23
