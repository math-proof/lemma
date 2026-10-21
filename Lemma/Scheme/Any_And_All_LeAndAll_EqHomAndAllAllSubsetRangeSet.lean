import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_exists_smooth_maximal_and_image_eq_of_iso_over](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_smooth_maximal_and_image_eq_of_iso_over.lean)
-/
@[path]
private lemma main
  {X S : (Scheme : Type (u + 1))} (f : X ⟶ S) (n : ℕ)
  (hdim : ∀ V : X.Opens, Smooth (V.ι ≫ f) → SmoothOfRelativeDimension n (V.ι ≫ f)) :
  -- imply
  ∃ U : X.Opens, SmoothOfRelativeDimension n (U.ι ≫ f) ∧ (∀ V : X.Opens, Smooth (V.ι ≫ f) → V ≤ U) ∧ (∀ w : X ≅ X, w.hom ≫ f = f → w.hom ''ᵁ U = U) ∧ (∀ w : X ≅ X, w.hom ≫ f = f → ∀ (T : (Scheme : Type (u + 1))) (ε : T ⟶ X), Set.range ε.base ⊆ (U : Set X) → Set.range (ε ≫ w.hom).base ⊆ (U : Set X)) := by
  -- proof
  classical
  let ι : Type u := Subtype (fun V : X.Opens => Smooth (V.ι ≫ f))
  let U : X.Opens := ⨆ V : ι, V.1
  have hU_max : ∀ V : X.Opens, Smooth (V.ι ≫ f) → V ≤ U :=
    fun V hV => le_iSup (fun V : ι => V.1) ⟨V, hV⟩
  have hres : ∀ {Y : (Scheme : Type (u + 1))} (g : Y ⟶ X) [IsOpenImmersion g] (V : X.Opens), Smooth (V.ι ≫ f) → Smooth (Scheme.Opens.ι ((TopologicalSpace.Opens.map g.base).obj V) ≫ g ≫ f) := by
    intro Y g _ V hV
    have e : Scheme.Opens.ι ((TopologicalSpace.Opens.map g.base).obj V) ≫ g ≫ f = morphismRestrict g V ≫ V.ι ≫ f := by
      rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    rw [e]
    apply IsZariskiLocalAtSource.comp hV _
  have hU_smooth : Smooth (U.ι ≫ f) := by
    apply IsZariskiLocalAtSource.of_iSup_eq_top (fun V : ι => (TopologicalSpace.Opens.map U.ι.base).obj V.1)
    ·
      rw [← Scheme.Hom.preimage_iSup]
      apply U.ι_preimage_self
    ·
      intro V
      apply hres U.ι V.1 V.2
  have hpre_le : ∀ w : X ≅ X, w.hom ≫ f = f → (TopologicalSpace.Opens.map w.hom.base).obj U ≤ U := by
    intro w hw
    show (TopologicalSpace.Opens.map w.hom.base).obj (⨆ V : ι, V.1) ≤ U
    rw [Scheme.Hom.preimage_iSup]
    refine iSup_le fun V => hU_max _ ?_
    have h := hres w.hom V.1 V.2
    rwa [hw] at h
  have hpre : ∀ w : X ≅ X, w.hom ≫ f = f → (TopologicalSpace.Opens.map w.hom.base).obj U = U := by
    intro w hw
    have hw' : w.inv ≫ f = f := by
      rw [Iso.inv_comp_eq, hw]
    have h1 : (TopologicalSpace.Opens.map w.inv.base).obj U ≤ U := hpre_le w.symm hw'
    refine le_antisymm (hpre_le w hw) ?_
    intro x hx
    show w.hom.base x ∈ (U : Set X)
    apply h1
    show (w.hom ≫ w.inv).base x ∈ (U : Set X)
    rw [Iso.hom_inv_id]
    apply hx
  refine ⟨U, hdim U hU_smooth, hU_max, ?_, ?_⟩
  ·
    intro w hw
    have hw' : w.inv ≫ f = f := by
      rw [Iso.inv_comp_eq, hw]
    ext x
    constructor
    ·
      rintro ⟨y, hy, rfl⟩
      have h : y ∈ (TopologicalSpace.Opens.map w.hom.base).obj U := by
        rw [hpre w hw]
        apply hy
      refine h
    ·
      intro hx
      refine ⟨w.inv.base x, ?_, ?_⟩
      ·
        have h : x ∈ (TopologicalSpace.Opens.map w.symm.hom.base).obj U := by
          rw [hpre w.symm hw']
          apply hx
        refine h
      ·
        show (w.inv ≫ w.hom).base x = x
        rw [Iso.inv_hom_id]
        rfl
  ·
    intro w hw T ε hε
    rintro _ ⟨t, rfl⟩
    have ht : ε.base t ∈ U := hε ⟨t, rfl⟩
    have h2 : ε.base t ∈ (TopologicalSpace.Opens.map w.hom.base).obj U := by
      rw [hpre w hw]
      apply ht
    refine h2


-- created on 2026-10-20
