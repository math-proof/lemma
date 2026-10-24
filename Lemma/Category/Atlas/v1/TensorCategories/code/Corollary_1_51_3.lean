import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.Corollary_1_51_3
open CategoryTheory MonoidalCategory Category


namespace CategoryTheory

/--
[rightDualTensorIso'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_51_3.lean)
-/
@[path]
lemma rightDualTensorIso'
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {X Y : C} :
-- imply
  Nonempty (HasRightDual.rightDual (X ⊗ Y) ≅ HasRightDual.rightDual Y ⊗ HasRightDual.rightDual X) := by
-- proof
  have adj1 := tensorRightAdjunction (X ⊗ Y) ((X ⊗ Y)ᘁ)
  have comp_adj := (tensorRightAdjunction X (Xᘁ : C)).comp (tensorRightAdjunction Y (Yᘁ : C))
  have assoc1 : tensorRight X ⋙ tensorRight Y ≅ tensorRight (X ⊗ Y) :=
    NatIso.ofComponents (fun Z => (α_ Z X Y)) (by intros; simp [tensorRight])
  have assoc2 : tensorRight (Yᘁ : C) ⋙ tensorRight (Xᘁ : C) ≅
    tensorRight ((Yᘁ : C) ⊗ (Xᘁ : C)) :=
    NatIso.ofComponents (fun Z => (α_ Z Yᘁ Xᘁ)) (by intros; simp [tensorRight])
  have adj2 := (comp_adj.ofNatIsoLeft assoc1).ofNatIsoRight assoc2
  exact ⟨(λ_ ((X ⊗ Y)ᘁ)).symm ≪≫
    (Adjunction.rightAdjointUniq adj1 adj2).app (𝟙_ C) ≪≫
    (λ_ ((Yᘁ : C) ⊗ (Xᘁ : C)))⟩

end CategoryTheory

namespace CategoryTheory

/--
[Corollary_1_51_3_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_51_3.lean)
-/
@[path]
lemma Corollary_1_51_3_simple
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  (C)
  [HasDistinguishedInvData C]
  [Limits.HasZeroMorphisms C]
  {L : C}
  [Simple L] :
-- imply
  Nonempty (doubleDualObj L ≅ HasRightDual.rightDual (distinguishedObj (C := C)) ⊗ L ⊗ distinguishedObj (C := C)) := by
-- proof
  unfold doubleDualObj
  obtain ⟨φ₁⟩ := simpleIsoTensorD_axiom' L
  obtain ⟨φ₂⟩ := rightDualTensorIso' L (distinguishedObj (C := C))
  obtain ⟨φ₃⟩ := simpleIsoTensorD_axiom' L
  letI : ExactPairing (HasRightDual.rightDual L) (doubleDualObj L) := HasRightDual.exact
  letI ep₂ : ExactPairing (L ⊗ distinguishedObj (C := C)) (doubleDualObj L) :=
    exactPairingCongrLeft φ₁.symm
  letI ep₃ : ExactPairing (L ⊗ distinguishedObj (C := C))
    (HasRightDual.rightDual (L ⊗ distinguishedObj (C := C))) := HasRightDual.exact
  let ψ₁ : doubleDualObj L ≅ HasRightDual.rightDual (L ⊗ distinguishedObj (C := C)) :=
    rightDualIso ep₂ ep₃
  let ψ₃ : HasRightDual.rightDual (distinguishedObj (C := C)) ⊗ HasRightDual.rightDual L ≅
    HasRightDual.rightDual (distinguishedObj (C := C)) ⊗ (L ⊗ distinguishedObj (C := C)) :=
    tensorIso (Iso.refl _) φ₃
  exact ⟨ψ₁.trans (φ₂.trans ψ₃)⟩

end CategoryTheory


-- created on 2026-10-23
