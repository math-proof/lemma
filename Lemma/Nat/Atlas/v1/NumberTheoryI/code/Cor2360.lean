import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[corollary_23_60](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2360.lean)
-/
@[path]
lemma corollary_23_60
  {R : Type u}
  [CommRing R]
  {M₁ M₂ M₃ : Type u}
  [AddCommGroup M₁]
  [AddCommGroup M₂]
  [AddCommGroup M₃]
  [Module R M₁]
  [Module R M₂]
  [Module R M₃]
  {f : M₁ →ₗ[R] M₂}
  {g : M₂ →ₗ[R] M₃}
  {A : Type u}
  [AddCommGroup A]
  [Module R A]
-- given
  (_hf : Function.Injective f)
  (hfg : Function.Exact f g)
  (hg : Function.Surjective g) :
-- imply
  Function.Injective (LinearMap.lcomp R A g) ∧ Function.Exact (LinearMap.lcomp R A g) (LinearMap.lcomp R A f) :=
-- proof
  ⟨LinearMap.lcomp_injective_of_surjective g hg,
    LinearMap.exact_lcomp_of_exact_of_surjective A hfg hg⟩


-- created on 2026-10-23
