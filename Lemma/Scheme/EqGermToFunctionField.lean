import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_exists_ringEquiv_functionField_germToFunctionField_eq_of_isIso](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_ringEquiv_functionField_germToFunctionField_eq_of_isIso.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsIso f] :
  -- imply
  ∃ ι : RingEquiv Y.functionField X.functionField, ∀ (V : Y.Opens) [Nonempty (V : (Scheme : Type (u + 1)))] [Nonempty ((TopologicalSpace.Opens.map f.base).obj V : (Scheme : Type (u + 1)))] (t : Y.presheaf.obj (Opposite.op V)), ι (Y.germToFunctionField V t) = X.germToFunctionField ((TopologicalSpace.Opens.map f.base).obj V) (f.app V t) := by
  -- proof
  have hgen : f.base (genericPoint X) = genericPoint Y := genericPoint_eq_of_isOpenImmersion f
  let e₁ : Y.presheaf.stalk (genericPoint Y) ≅ Y.presheaf.stalk (f.base (genericPoint X)) :=
    Y.presheaf.stalkCongr (.of_eq hgen.symm)
  let e₂ : Y.presheaf.stalk (f.base (genericPoint X)) ≅ X.presheaf.stalk (genericPoint X) :=
    asIso (f.stalkMap (genericPoint X))
  refine ⟨(Iso.trans e₁ e₂).commRingCatIsoToRingEquiv, ?_⟩
  intro V _ _ t
  have hmem : f.base (genericPoint X) ∈ V := by
    rw [hgen]
    apply ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty (V : (Scheme : Type (u + 1)))›)
  change (Iso.trans e₁ e₂).hom (Y.presheaf.germ V (genericPoint Y) _ t) = X.presheaf.germ ((TopologicalSpace.Opens.map f.base).obj V) (genericPoint X) _ (f.app V t)
  simp only [Iso.trans_hom, CommRingCat.comp_apply, e₁, e₂, asIso_hom]
  have h1 : (Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom (Y.presheaf.germ V (genericPoint Y) (((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty (V : (Scheme : Type (u + 1)))›)) t) = Y.presheaf.germ V (f.base (genericPoint X)) hmem t := by
    simp only [TopCat.Presheaf.stalkCongr_hom]
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  rw [h1, Scheme.Hom.germ_stalkMap_apply]


-- created on 2026-10-20
