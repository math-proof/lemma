import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

/--
[AlgebraicGeometry_Scheme_Modules_existsUnique_hom_app_eq_of_iSup_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_existsUnique_hom_app_eq_of_iSup_eq_top.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type (u + 1))} (M N : X.Modules) {ι : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤)
  (f : ∀ (W : X.Opens), (∃ i, W ≤ U i) → LinearMap (RingHom.id (X.presheaf.obj (op W))) ((Scheme.Modules.presheaf M).obj (op W)) ((Scheme.Modules.presheaf N).obj (op W)))
  (hf : ∀ (W W' : X.Opens) (hW : ∃ i, W ≤ U i) (h : W' ≤ W) (x : (Scheme.Modules.presheaf M).obj (op W)), N.presheaf.map (homOfLE h).op (f W hW x) = f W' (hW.imp fun _ hi => h.trans hi) (M.presheaf.map (homOfLE h).op x)) :
  ∃! F : M ⟶ N, ∀ (W : X.Opens) (hW : ∃ i, W ≤ U i) (x : (Scheme.Modules.presheaf M).obj (op W)), F.app W x = f W hW x := by
  classical
  let β : Type u := Subtype (fun W : X.Opens => ∃ i, W ≤ U i)
  let B : β → X.Opens := fun b => b.1
  have hB : TopologicalSpace.Opens.IsBasis (Set.range B) :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {W} {x} hx => by
      have hx' : x ∈ iSup U := by
        rw [hU]
        trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
      exact ⟨W ⊓ U i, ⟨⟨W ⊓ U i, i, inf_le_right⟩, rfl⟩, ⟨hx, hi⟩, inf_le_left⟩
  let N' : TopCat.Sheaf Ab X := ⟨N.val.presheaf, N.isSheaf⟩
  have hext : ∀ (V : X.Opens) (a c : (Scheme.Modules.presheaf N).obj (op V)), (∀ (b : β) (hbV : B b ≤ V), N.presheaf.map (homOfLE hbV).op a = N.presheaf.map (homOfLE hbV).op c) → a = c := by
    intro V a c h
    have hcov : V ≤ iSup (fun k : Subtype (fun b : β => B b ≤ V) => B k.1) := by
      intro x hx
      obtain ⟨W', ⟨b, rfl⟩, hxW', hW'V⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp hB hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨b, hW'V⟩, hxW'⟩
    refine N'.eq_of_locally_eq' (fun k : Subtype (fun b : β => B b ≤ V) => B k.1) V (fun k => homOfLE k.2) hcov a c
      (fun k => h k.1 k.2)
  let α : (inducedFunctor B).op ⋙ M.val.presheaf ⟶ (inducedFunctor B).op ⋙ N.val.presheaf :=
    { app := fun b => AddCommGrpCat.ofHom (f (B b.unop) b.unop.2).toAddMonoidHom
      naturality := fun {b b'} g => by
        ext x
        apply (hf (B b.unop) (B b'.unop) b.unop.2 g.unop.hom.le x).symm }
  obtain ⟨φ, hφ⟩ : ∃ φ : M.val.presheaf ⟶ N.val.presheaf, ∀ b : β, φ.app (op (B b)) = α.app (op b) :=
    ⟨TopCat.Sheaf.restrictHomEquivHom M.val.presheaf N' hB α, TopCat.Sheaf.extend_hom_app M.val.presheaf N' hB α⟩
  let φ' : ∀ V : X.Opens, (Scheme.Modules.presheaf M).obj (op V) → (Scheme.Modules.presheaf N).obj (op V) := fun V x => φ.app (op V) x
  have hφ' : ∀ (b : β) (x : (Scheme.Modules.presheaf M).obj (op (B b))), φ' (B b) x = f (B b) b.2 x := fun b x => by
    change φ.app (op (B b)) x = _
    rw [hφ b]
    rfl
  have hnat : ∀ (V V' : X.Opens) (h : V' ≤ V) (x : (Scheme.Modules.presheaf M).obj (op V)), N.presheaf.map (homOfLE h).op (φ' V x) = φ' V' (M.presheaf.map (homOfLE h).op x) :=
    fun V V' h x => (NatTrans.naturality_apply φ (homOfLE h).op x).symm
  have hlin : ∀ (V : X.Opens) (r : X.presheaf.obj (op V)) (m : (Scheme.Modules.presheaf M).obj (op V)), φ' V (r • m) = r • φ' V m := by
    intro V r m
    apply hext V
    intro b hbV
    rw [hnat, Scheme.Modules.map_smul, hφ', map_smul, Scheme.Modules.map_smul, hnat, hφ']
  let F : M ⟶ N := ⟨PresheafOfModules.homMk φ fun W r m => hlin W.unop r m⟩
  have hF : ∀ (W : X.Opens) (hW : ∃ i, W ≤ U i) (x : (Scheme.Modules.presheaf M).obj (op W)), F.app W x = f W hW x :=
    fun W hW x => hφ' ⟨W, hW⟩ x
  refine ⟨F, hF, fun G hG => ?_⟩
  apply (Scheme.Modules.toPresheaf X).map_injective
  refine TopCat.Sheaf.hom_ext M.val.presheaf N' hB fun b => ?_
  ext x
  change G.app (B b) x = F.app (B b) x
  rw [hG (B b) b.2 x, hF (B b) b.2 x]


-- created on 2026-10-20
