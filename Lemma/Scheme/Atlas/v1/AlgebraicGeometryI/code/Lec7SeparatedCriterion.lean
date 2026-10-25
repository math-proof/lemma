import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec7SeparatedCriterion
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


/--
[isAffineHom_diagonal_iff_of_affine_target](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7SeparatedCriterion.lean)
-/
@[path]
lemma isAffineHom_diagonal_iff_of_affine_target
  {X : Scheme.{u}}
  {k : Type u}
  [Field k]
  {f : X ⟶ Spec (.of k)}
  {S : Scheme.{u}}
  [IsAffine S]
  {g : X ⟶ S} :
-- imply
  IsAffineHom (pullback.diagonal g) ↔ ∀ (V₁ V₂ : X.Opens), IsAffineOpen V₁ → IsAffineOpen V₂ → IsAffineOpen (V₁ ⊓ V₂) := by
-- proof
  rw [isAffineHom_diagonal_iff]
  constructor
  · intro h V₁ V₂ hV₁ hV₂
    exact h ⊤ (isAffineOpen_top _) V₁ (by simp) V₂ (by simp) hV₁ hV₂
  · intro h U _ V₁ _ V₂ _ hV₁ hV₂
    exact h V₁ V₂ hV₁ hV₂

/--
[prop9_separated_imp_affine_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7SeparatedCriterion.lean)
-/
@[path]
lemma prop9_separated_imp_affine_intersection
  {X : Scheme.{u}}
  {k : Type u}
  [Field k]
  {f : X ⟶ Spec (.of k)}
  [IsSeparated f]
  {U V : X.Opens}
-- given
  (hU : IsAffineOpen U)
  (hV : IsAffineOpen V) :
-- imply
  IsAffineOpen (U ⊓ V) := by
-- proof
  have hAff : IsAffineHom (pullback.diagonal f) :=
    (isClosedImmersion_iff_isAffineHom.mp ((isSeparated_iff f).mp ‹_›)).1
  exact isAffineHom_diagonal_iff.mp hAff ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV

/--
[prop9_affine_diagonal_iff_affine_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7SeparatedCriterion.lean)
-/
@[path]
lemma prop9_affine_diagonal_iff_affine_intersection
  {X : Scheme.{u}}
  {k : Type u}
  [Field k]
  {f : X ⟶ Spec (.of k)} :
-- imply
  IsAffineHom (pullback.diagonal f) ↔ ∀ (U V : X.Opens), IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) :=
-- proof
  isAffineHom_diagonal_iff_of_affine_target
/-- Lec 7, Prop 9: `f : X → Spec k` is separated iff (i) intersections
of affine opens of `X` are affine and (ii) on every such intersection
the restrictions from each side generate the ring of sections. -/


-- created on 2026-10-23
