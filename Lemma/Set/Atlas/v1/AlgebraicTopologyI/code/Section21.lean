import Mathlib
import Initialize.Tactic.Attr.Basic


namespace TensorProductsAndTor

/--
[tensor_right_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section21.lean)
-/
@[path]
lemma tensor_right_exact
  [CommRing R]
  [AddCommGroup N']
  [AddCommGroup N]
  [AddCommGroup N'']
  [Module R N']
  [Module R N]
  [Module R N'']
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  {f : N' →ₗ[R] N}
  {g : N →ₗ[R] N''}
-- given
  (hfg : Function.Exact f g)
  (hg : Function.Surjective g) :
-- imply
  Function.Exact (LinearMap.lTensor M f) (LinearMap.lTensor M g) ∧ Function.Surjective (LinearMap.lTensor M g) :=
-- proof
  ⟨lTensor_exact M hfg hg, LinearMap.lTensor_surjective M hg⟩

end TensorProductsAndTor

namespace TensorProductsAndTor

/--
[directSum_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section21.lean)
-/
@[path]
lemma directSum_exact
  [Semiring R]
  {M' : ι → Type*}
  [∀ i, AddCommMonoid (M' i)]
  [∀ i, Module R (M' i)]
  {M : ι → Type*}
  [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)]
  {M'' : ι → Type*}
  [∀ i, AddCommMonoid (M'' i)]
  [∀ i, Module R (M'' i)]
-- given
  (f : ∀ i, M' i →ₗ[R] M i)
  (g : ∀ i, M i →ₗ[R] M'' i)
  (hexact : ∀ i, Function.Exact (f i) (g i)) :
-- imply
  Function.Exact (DirectSum.lmap f) (DirectSum.lmap g) := by
-- proof
  rw [LinearMap.exact_iff, DirectSum.ker_lmap, DirectSum.range_lmap]
  congr 1
  simp_rw [fun i => LinearMap.exact_iff.mp (hexact i)]

end TensorProductsAndTor


-- created on 2026-10-23
