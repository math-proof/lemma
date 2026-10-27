import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[nondegenerate_of_orthogonal_top_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/BilinFormComplementation.lean)
-/
@[path]
private lemma main
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
-- given
  (href : B.IsRefl)
  (hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥) :
-- imply
  B.Nondegenerate :=
-- proof
  href.nondegenerate_iff_separatingLeft.mpr
    (LinearMap.separatingLeft_iff_ker_eq_bot.mpr
      (by rwa [LinearMap.BilinForm.orthogonal_top_eq_ker href] at hnd))



/--
[orthogonal_top_eq_bot_of_nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/BilinFormComplementation.lean)
-/
private lemma orthogonal_top_eq_bot_of_nondegenerate
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
-- given
  (href : B.IsRefl)
  (hnd : B.Nondegenerate) :
-- imply
  LinearMap.BilinForm.orthogonal B ⊤ = ⊥ := by
-- proof
  rwa [LinearMap.BilinForm.orthogonal_top_eq_ker href]



/--
[isCompl_span_singleton_orthogonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/BilinFormComplementation.lean)
-/
private lemma isCompl_span_singleton_orthogonal
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
  {x : V}
-- given
  (hx : ¬ LinearMap.BilinForm.IsOrtho B x x) :
-- imply
  IsCompl (k ∙ x) (LinearMap.BilinForm.orthogonal B (k ∙ x)) :=
-- proof
  LinearMap.BilinForm.isCompl_span_singleton_orthogonal hx



/--
[restrict_nondegenerate_orthogonal_spanSingleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/BilinFormComplementation.lean)
-/
private lemma restrict_nondegenerate_orthogonal_spanSingleton
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
  {x : V}
-- given
  (href : B.IsRefl)
  (hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥)
  (hx : ¬ LinearMap.BilinForm.IsOrtho B x x) :
-- imply
  (LinearMap.BilinForm.restrict B (LinearMap.BilinForm.orthogonal B (k ∙ x))).Nondegenerate :=
-- proof
  LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton B
    (nondegenerate_of_orthogonal_top_eq_bot B href hnd) href hx
variable {k : Type*} [Field k]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]



/--
[orthogonal_isCompl_of_restrict_nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/BilinFormComplementation.lean)
-/
private lemma orthogonal_isCompl_of_restrict_nondegenerate
  [Field k]
  {B : LinearMap.BilinForm k V}
  {S : Submodule k V}
-- given
  (href : ∀ x y : V, B x y = 0 → B y x = 0)
  (hS : (LinearMap.BilinForm.restrict B S).Nondegenerate) :
-- imply
  IsCompl S (LinearMap.BilinForm.orthogonal B S) :=
-- proof
  LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate href hS



-- created on 2026-10-23
-- updated on 2026-10-26
