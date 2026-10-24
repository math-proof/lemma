import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.DistinguishedInvertible
open CategoryTheory MonoidalCategory Category Limits TensorCategories CategoryTheory.HasDistinguishedInvertible


namespace CategoryTheory

/--
[dualOfProjectiveIsProjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DistinguishedInvertible.lean)
-/
@[path]
lemma dualOfProjectiveIsProjective
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {P : C}
  [Projective P]
  [Projective (𝟙_ C)] :
-- imply
  Projective (HasRightDual.rightDual P) where factors {E X} f e _ := by
-- proof
  let Φ := tensorLeftHomEquiv (𝟙_ C) P (HasRightDual.rightDual P)
  let f₁ : HasRightDual.rightDual P ⊗ 𝟙_ C ⟶ X := (ρ_ _).hom ≫ f
  let f₂ : 𝟙_ C ⟶ P ⊗ X := Φ X f₁
  have adj : tensorLeft P ⊣ tensorLeft (ᘁP) := tensorLeftAdjunction (ᘁP) P
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft P) :=
    adj.leftAdjoint_preservesColimits
  have : (tensorLeft P).PreservesEpimorphisms :=
    preservesEpimorphisms_of_preservesColimitsOfShape _
  have : Epi (P ◁ e) := (tensorLeft P).map_epi e
  obtain ⟨g₂, hg₂⟩ := Projective.factors f₂ (P ◁ e)
  let g₁ : HasRightDual.rightDual P ⊗ 𝟙_ C ⟶ E := (Φ E).symm g₂
  use (ρ_ _).inv ≫ g₁
  have key : g₁ ≫ e = f₁ := by
    apply (Φ X).injective
    rw [tensorLeftHomEquiv_naturality g₁ e]
    change (Φ E) g₁ ≫ P ◁ e = (Φ X) f₁
    simp only [g₁, Equiv.apply_symm_apply]
    exact hg₂
  simp only [assoc, key, f₁, Iso.inv_hom_id_assoc]

end CategoryTheory

namespace CategoryTheory.HasDistinguishedInvertible

/--
[rightDualTensorIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DistinguishedInvertible.lean)
-/
@[path]
lemma rightDualTensorIso
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  (C)
  (C)
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C] :
-- imply
  ∀ (X Y : C), Nonempty (HasRightDual.rightDual (X ⊗ Y) ≅ HasRightDual.rightDual Y ⊗ HasRightDual.rightDual X) := by
-- proof
  intro X Y
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
/-- Corollary 1.51.3 (projective case): the double dual of a projective `P` is
isomorphic to `D^* ⊗ P ⊗ D`. -/

end CategoryTheory.HasDistinguishedInvertible


-- created on 2026-10-23
