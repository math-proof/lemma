import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.SeparatedMorphismUniqueness
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace AlgebraicGeometry

/--
[eq_of_agree_on_nonempty_open](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SeparatedMorphismUniqueness.lean)
-/
@[path]
lemma eq_of_agree_on_nonempty_open
  {X Y : Scheme.{u}}
  [IrreducibleSpace X]
  [IsReduced X]
  [Y.IsSeparated]
  {f g : X ⟶ Y}
  {U : X.Opens}
-- given
  (hU_ne : (U : Set X).Nonempty)
  (h_agree : U.ι ≫ f = U.ι ≫ g) :
-- imply
  f = g := by
-- proof
  have hU_dense : Dense (X := X) (U : Set X) := U.isOpen.dense hU_ne
  haveI : IsDominant U.ι := Scheme.PartialMap.Opens.isDominant_ι hU_dense
  exact ext_of_isDominant U.ι h_agree

end AlgebraicGeometry

namespace AlgebraicGeometry

/--
[eq_of_agree_on_nonempty_open_over_base](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SeparatedMorphismUniqueness.lean)
-/
@[path]
lemma eq_of_agree_on_nonempty_open_over_base
  {X Y S : Scheme.{u}}
  [IrreducibleSpace X]
  [IsReduced X]
  {s : Y ⟶ S}
  [IsSeparated s]
  {g h : X ⟶ Y}
  {U : X.Opens}
-- given
  (hs : g ≫ s = h ≫ s)
  (hU_ne : (U : Set X).Nonempty)
  (h_agree : U.ι ≫ g = U.ι ≫ h) :
-- imply
  g = h := by
-- proof
  have hU_dense : Dense (X := X) (U : Set X) := U.isOpen.dense hU_ne
  haveI : IsDominant U.ι := Scheme.PartialMap.Opens.isDominant_ι hU_dense
  exact ext_of_isDominant_of_isSeparated s hs U.ι h_agree
end AlgebraicGeometry



-- created on 2026-10-23
