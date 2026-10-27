import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma Scheme.iSup_affineOpens_le
  {X : (Scheme : Type (u + 1))}
  (U : X.Opens) :
    iSup (fun V : Subtype (fun V : X.Opens => IsAffineOpen V ∧ V ≤ U) => (V : X.Opens)) = U := by
  apply le_antisymm
  ·
    apply iSup_le
    exact fun V => V.2.2
  ·
    intro x hx
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := U) hx
    apply Opens.mem_iSup.mpr ⟨⟨W, hW, hWU⟩, hxW⟩
private lemma Scheme.Hom.app_apply_map_homOfLE
  {X Y : (Scheme : Type (u + 1))}
  (f : Y ⟶ X) {U V : X.Opens}
  (e : V ≤ U)
    (s : X.presheaf.obj (op U)) :
    f.app V (X.presheaf.map (homOfLE e).op s) =
      Y.presheaf.map (homOfLE (show ((TopologicalSpace.Opens.map f.base).obj V) ≤ ((TopologicalSpace.Opens.map f.base).obj U) from fun _ hx => e hx)).op (f.app U s) := by
  have h := CategoryTheory.ConcreteCategory.congr_hom (f.naturality (homOfLE e).op) s
  rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply] at h
  rw [h]
  rfl
private lemma Scheme.Hom.app_prod_injective_of_forall_isAffineOpen
  {X Y₁ Y₂ : (Scheme : Type (u + 1))}
  (i₁ : Y₁ ⟶ X)
    (i₂ : Y₂ ⟶ X) (U : X.Opens)
    (h : ∀ V : X.Opens, IsAffineOpen V → V ≤ U → Function.Injective (fun f : X.presheaf.obj (op V) => ((i₁.app V) f, (i₂.app V) f)))
    {W : X.Opens} (hW : W ≤ U) :
    Function.Injective (fun f : X.presheaf.obj (op W) => ((i₁.app W) f, (i₂.app W) f)) := by
  intro f f' hff'
  simp only [Prod.mk.injEq] at hff'
  fapply X.sheaf.eq_of_locally_eq' (fun V : Subtype (fun V : X.Opens => IsAffineOpen V ∧ V ≤ W) => (V : X.Opens)) W
    (fun V => homOfLE V.2.2) (le_of_eq (Scheme.iSup_affineOpens_le W).symm)
  intro V
  change X.presheaf.map (homOfLE V.2.2).op f = X.presheaf.map (homOfLE V.2.2).op f'
  apply h V.1 V.2.1 (V.2.2.trans hW)
  simp only [Prod.mk.injEq]
  constructor
  · rw [Scheme.Hom.app_apply_map_homOfLE, Scheme.Hom.app_apply_map_homOfLE, hff'.1]
  · rw [Scheme.Hom.app_apply_map_homOfLE, Scheme.Hom.app_apply_map_homOfLE, hff'.2]
private lemma Scheme.Hom.app_apply_map_op
  {X Y : (Scheme : Type (u + 1))}
  (f : Y ⟶ X) {U V : X.Opens}
  (ι : V ⟶ U)
    (s : X.presheaf.obj (op U)) :
    f.app V (X.presheaf.map ι.op s) =
      Y.presheaf.map ((Opens.map f.base).map ι).op (f.app U s) := by
  have h := CategoryTheory.ConcreteCategory.congr_hom (f.naturality ι.op) s
  rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply] at h
  apply h
/--
[AlgebraicGeometry_Scheme_Hom_app_injective_and_exists_of_forall_isAffineOpen](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_app_injective_and_exists_of_forall_isAffineOpen.lean)
-/
@[path]
private lemma main
  {X Y₁ Y₂ : (Scheme : Type (u + 1))}
  (i₁ : Y₁ ⟶ X)
  (i₂ : Y₂ ⟶ X)
  (U : X.Opens)
    (h : ∀ (V : X.Opens), IsAffineOpen V → V ≤ U → Function.Injective (fun f : X.presheaf.obj (op V) => ((i₁.app V) f, (i₂.app V) f)) ∧ ∀ (g₁ : Y₁.presheaf.obj (op ((TopologicalSpace.Opens.map i₁.base).obj V))) (g₂ : Y₂.presheaf.obj (op ((TopologicalSpace.Opens.map i₂.base).obj V))), (pullback i₁ i₂).presheaf.map (eqToHom (show ((TopologicalSpace.Opens.map (pullback.snd i₁ i₂).base).obj ((((TopologicalSpace.Opens.map i₂.base).obj V)))) = ((TopologicalSpace.Opens.map (pullback.fst i₁ i₂).base).obj ((((TopologicalSpace.Opens.map i₁.base).obj V)))) by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op ((pullback.fst i₁ i₂).app (((TopologicalSpace.Opens.map i₁.base).obj V)) g₁) = (pullback.snd i₁ i₂).app (((TopologicalSpace.Opens.map i₂.base).obj V)) g₂ → ∃ f : X.presheaf.obj (op V), (i₁.app V) f = g₁ ∧ (i₂.app V) f = g₂) :
    Function.Injective (fun f : X.presheaf.obj (op U) => ((i₁.app U) f, (i₂.app U) f)) ∧ ∀ (g₁ : Y₁.presheaf.obj (op ((TopologicalSpace.Opens.map i₁.base).obj U))) (g₂ : Y₂.presheaf.obj (op ((TopologicalSpace.Opens.map i₂.base).obj U))), (pullback i₁ i₂).presheaf.map (eqToHom (show ((TopologicalSpace.Opens.map (pullback.snd i₁ i₂).base).obj ((((TopologicalSpace.Opens.map i₂.base).obj U)))) = ((TopologicalSpace.Opens.map (pullback.fst i₁ i₂).base).obj ((((TopologicalSpace.Opens.map i₁.base).obj U)))) by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op ((pullback.fst i₁ i₂).app (((TopologicalSpace.Opens.map i₁.base).obj U)) g₁) = (pullback.snd i₁ i₂).app (((TopologicalSpace.Opens.map i₂.base).obj U)) g₂ → ∃ f : X.presheaf.obj (op U), (i₁.app U) f = g₁ ∧ (i₂.app U) f = g₂ := by
  classical
  have hinj : ∀ W : X.Opens, W ≤ U → Function.Injective (fun f : X.presheaf.obj (op W) => ((i₁.app W) f, (i₂.app W) f)) :=
    fun W hW => Scheme.Hom.app_prod_injective_of_forall_isAffineOpen i₁ i₂ U (fun V hV hVU => (h V hV hVU).1) hW
  refine ⟨hinj U le_rfl, ?_⟩
  intro g₁ g₂ hagree
  let ι : Type u := Subtype (fun V : X.Opens => IsAffineOpen V ∧ V ≤ U)
  let V : ι → X.Opens := fun j => j.1
  let r₁ : ∀ j : ι, Y₁.presheaf.obj (op ((TopologicalSpace.Opens.map i₁.base).obj (V j))) := fun j =>
    Y₁.presheaf.map (homOfLE (i₁.preimage_mono j.2.2)).op g₁
  let r₂ : ∀ j : ι, Y₂.presheaf.obj (op ((TopologicalSpace.Opens.map i₂.base).obj (V j))) := fun j =>
    Y₂.presheaf.map (homOfLE (i₂.preimage_mono j.2.2)).op g₂
  have hagreeV : ∀ j : ι, (pullback i₁ i₂).presheaf.map (eqToHom (show ((TopologicalSpace.Opens.map (pullback.snd i₁ i₂).base).obj ((((TopologicalSpace.Opens.map i₂.base).obj (V j))))) = ((TopologicalSpace.Opens.map (pullback.fst i₁ i₂).base).obj ((((TopologicalSpace.Opens.map i₁.base).obj (V j))))) by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op ((pullback.fst i₁ i₂).app (((TopologicalSpace.Opens.map i₁.base).obj (V j))) (r₁ j)) = (pullback.snd i₁ i₂).app (((TopologicalSpace.Opens.map i₂.base).obj (V j))) (r₂ j) := by
    intro j
    simp only [r₁, r₂]
    rw [Scheme.Hom.app_apply_map_op, Scheme.Hom.app_apply_map_op, ← hagree]
    generalize (pullback.fst i₁ i₂).app (((TopologicalSpace.Opens.map i₁.base).obj U)) g₁ = t
    rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    congr 1
  choose fV hfV₁ hfV₂ using fun j : ι => (h (V j) j.2.1 j.2.2).2 (r₁ j) (r₂ j) (hagreeV j)
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 V fV := by
    intro j j'
    apply hinj (V j ⊓ V j') (inf_le_left.trans j.2.2)
    change ((i₁.app _) (X.presheaf.map _ (fV j)), (i₂.app _) (X.presheaf.map _ (fV j))) =
      ((i₁.app _) (X.presheaf.map _ (fV j')), (i₂.app _) (X.presheaf.map _ (fV j')))
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    ·
      rw [Scheme.Hom.app_apply_map_op, Scheme.Hom.app_apply_map_op, hfV₁, hfV₁]
      rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      congr 1
    ·
      rw [Scheme.Hom.app_apply_map_op, Scheme.Hom.app_apply_map_op, hfV₂, hfV₂]
      rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      congr 1
  obtain ⟨f, hf, -⟩ := X.sheaf.existsUnique_gluing' V U (fun j => homOfLE j.2.2)
    (le_of_eq (Scheme.iSup_affineOpens_le U).symm) fV hcompat
  refine ⟨f, ?_, ?_⟩
  ·
    fapply Y₁.sheaf.eq_of_locally_eq' (fun j : ι => ((TopologicalSpace.Opens.map i₁.base).obj (V j))) (((TopologicalSpace.Opens.map i₁.base).obj U))
      (fun j => homOfLE (i₁.preimage_mono j.2.2))
    ·
      rw [← Scheme.Hom.preimage_iSup]
      apply i₁.preimage_mono (le_of_eq (Scheme.iSup_affineOpens_le U).symm)
    ·
      intro j
      have e1 : (i₁.app (V j)) (X.presheaf.map (homOfLE j.2.2).op f) = r₁ j := by
        have := hf j
        change X.presheaf.map (homOfLE j.2.2).op f = fV j at this
        rw [this, hfV₁]
      rw [Scheme.Hom.app_apply_map_op] at e1
      apply e1
  ·
    fapply Y₂.sheaf.eq_of_locally_eq' (fun j : ι => ((TopologicalSpace.Opens.map i₂.base).obj (V j))) (((TopologicalSpace.Opens.map i₂.base).obj U))
      (fun j => homOfLE (i₂.preimage_mono j.2.2))
    ·
      rw [← Scheme.Hom.preimage_iSup]
      apply i₂.preimage_mono (le_of_eq (Scheme.iSup_affineOpens_le U).symm)
    ·
      intro j
      have e2 : (i₂.app (V j)) (X.presheaf.map (homOfLE j.2.2).op f) = r₂ j := by
        have := hf j
        change X.presheaf.map (homOfLE j.2.2).op f = fV j at this
        rw [this, hfV₂]
      rw [Scheme.Hom.app_apply_map_op] at e2
      apply e2


-- created on 2026-10-20
