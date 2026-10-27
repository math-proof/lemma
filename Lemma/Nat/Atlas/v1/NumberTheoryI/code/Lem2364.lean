import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[tensor_rTensor_rightExact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem2364.lean)
-/
@[path]
lemma tensor_rTensor_rightExact
  [CommRing R]
  [AddCommGroup M]
  [AddCommGroup N]
  [AddCommGroup P]
  [Module R M]
  [Module R N]
  [Module R P]
  {A : Type*}
  [AddCommGroup A]
  [Module R A]
  {f : M →ₗ[R] N}
  {g : N →ₗ[R] P}
-- given
  (hfg : Function.Exact f g)
  (hg : Function.Surjective g) :
-- imply
  Function.Exact (LinearMap.rTensor A f) (LinearMap.rTensor A g) ∧ Function.Surjective (LinearMap.rTensor A g) :=
-- proof
  ⟨rTensor_exact A hfg hg, LinearMap.rTensor_surjective A hg⟩


-- created on 2026-10-23
