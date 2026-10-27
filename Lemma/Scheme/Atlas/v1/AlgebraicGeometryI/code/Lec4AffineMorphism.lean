import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec4AffineMorphism
open AlgebraicGeometry CategoryTheory


/--
[isAffineMorphism_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4AffineMorphism.lean)
-/
@[path]
lemma isAffineMorphism_iff
  {X Y : Scheme.{u}}
  {f : X ⟶ Y} :
-- imply
  IsAffineMorphism f ↔ ∀ (U : Y.Opens), IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U) :=
-- proof
  isAffineHom_iff f

/--
[isAffineMorphism_of_affine_open_cover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4AffineMorphism.lean)
-/
@[path]
lemma isAffineMorphism_of_affine_open_cover
  {X Y : Scheme.{u}}
  {f : X ⟶ Y}
-- given
  (H : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsAffineOpen U ∧ IsAffineOpen (f ⁻¹ᵁ U)) :
-- imply
  IsAffineMorphism f :=
-- proof
  isAffineHom_of_forall_exists_isAffineOpen f H


-- created on 2026-10-23
