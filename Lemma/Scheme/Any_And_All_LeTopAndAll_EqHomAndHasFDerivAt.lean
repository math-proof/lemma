import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[AlgebraicGeometry_IsClosedImmersion_exists_hasFDerivAt_appLE_comp_of_hasFDerivAt_appLE](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_exists_hasFDerivAt_appLE_comp_of_hasFDerivAt_appLE.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type 1)}
  (g : X ⟶ Y) [IsClosedImmersion g]
  (π : (Fin 2 → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ X))
  (v₀ : Fin 2 → ℂ)
  (U : X.Opens)
  (f₁ f₂ : X.presheaf.obj (op U))
  (ε : ℝ)
  (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
  (F : (Fin 2 → ℂ) → (Fin 2 → ℂ))
  -- given
  (hcont : ∀ W : X.Opens, ⊤ ≤ (TopologicalSpace.Opens.map (π v₀).base).obj W → ∃ ε' : ℝ, 0 < ε' ∧ ∀ v ∈ Metric.ball v₀ ε', ⊤ ≤ (TopologicalSpace.Opens.map (π v).base).obj W)
  (hε : 0 < ε)
  (hU : ∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (TopologicalSpace.Opens.map (π v).base).obj U)
  (hF : ∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ (TopologicalSpace.Opens.map (π v).base).obj U), v ∈ Metric.ball v₀ ε → F v = Matrix.vecCons ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π v).appLE U ⊤ h) f₁)) (Matrix.vecCons ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π v).appLE U ⊤ h) f₂)) Matrix.vecEmpty))
  (hD : HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀) :
  -- imply
  ∃ (V : Y.Opens) (f₂' f₃' : Y.presheaf.obj (op V)) (ε' : ℝ) (F' : (Fin 2 → ℂ) → (Fin 2 → ℂ)), 0 < ε' ∧ (∀ v ∈ Metric.ball v₀ ε', ⊤ ≤ (TopologicalSpace.Opens.map (π v ≫ g).base).obj V) ∧ (∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ (TopologicalSpace.Opens.map (π v ≫ g).base).obj V), v ∈ Metric.ball v₀ ε' → F' v = Matrix.vecCons ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π v ≫ g).appLE V ⊤ h) f₂')) (Matrix.vecCons ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π v ≫ g).appLE V ⊤ h) f₃')) Matrix.vecEmpty)) ∧ HasFDerivAt F' (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀ := by
  -- proof
  classical
  let p₀ := IsLocalRing.closedPoint ℂ
  have hp : ∀ p : (Spec (CommRingCat.of ℂ)).carrier, p = p₀ := fun p => Subsingleton.elim _ _
  have hle_iff : ∀ (Z : (Scheme : Type 1)) (q : Spec (CommRingCat.of ℂ) ⟶ Z) (W : Z.Opens), ⊤ ≤ (TopologicalSpace.Opens.map q.base).obj W ↔ q.base p₀ ∈ W := by
    intro Z q W
    constructor
    ·
      intro h
      apply h (x := p₀) trivial
    ·
      intro h p _
      rw [hp p]
      apply h
  set x₀ := (π v₀).base p₀
  have hx₀U : x₀ ∈ U := (hle_iff X (π v₀) U).mp (hU v₀ (Metric.mem_ball_self hε))
  obtain ⟨W, hW, hgxW, _⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := g.base x₀) (U := ⊤) trivial
  have hWpre : IsAffineOpen ((TopologicalSpace.Opens.map g.base).obj W) := hW.preimage g
  have hx₀W : x₀ ∈ (TopologicalSpace.Opens.map g.base).obj W := hgxW
  obtain ⟨rbar, hrbar_le, hx₀r⟩ := hWpre.exists_basicOpen_le (V := U ⊓ (TopologicalSpace.Opens.map g.base).obj W) ⟨x₀, ⟨hx₀U, hx₀W⟩⟩ hx₀W
  have hsurj : ∀ (V : Y.Opens), IsAffineOpen V → Function.Surjective (g.app V) := by
    intro V hV
    let _ : IsAffine V := hV
    let _ : IsClosedImmersion (morphismRestrict g V) :=
      IsZariskiLocalAtTarget.restrict (inferInstance : IsClosedImmersion g) V
    have h1 := (IsClosedImmersion.isAffine_surjective_of_isAffine (morphismRestrict g V)).2
    rw [Scheme.Hom.appTop, morphismRestrict_app'] at h1
    have e₁ := V.ι_image_top
    have e₂ := Scheme.Opens.ι_image_top ((TopologicalSpace.Opens.map g.base).obj V)
    have h2 := (Scheme.Hom.appLE_congr g _ e₁ e₂ (fun φ => Function.Surjective φ)).mp h1
    rwa [Scheme.Hom.appLE_eq_app] at h2
  obtain ⟨r, hr⟩ := hsurj W hW rbar
  have hVpre : (TopologicalSpace.Opens.map g.base).obj (Y.basicOpen r) = X.basicOpen rbar := by
    rw [Scheme.preimage_basicOpen, hr]
  have hVU : (TopologicalSpace.Opens.map g.base).obj (Y.basicOpen r) ≤ U := hVpre.le.trans (hrbar_le.trans inf_le_left)
  have hx₀V : x₀ ∈ (TopologicalSpace.Opens.map g.base).obj (Y.basicOpen r) := by
    rw [hVpre]
    apply hx₀r
  obtain ⟨f₂', hf₂'⟩ := hsurj (Y.basicOpen r) (hW.basicOpen r) (X.presheaf.map (homOfLE hVU).op f₁)
  obtain ⟨f₃', hf₃'⟩ := hsurj (Y.basicOpen r) (hW.basicOpen r) (X.presheaf.map (homOfLE hVU).op f₂)
  obtain ⟨ε₁, hε₁, hball⟩ := hcont ((TopologicalSpace.Opens.map g.base).obj (Y.basicOpen r)) ((hle_iff X (π v₀) _).mpr hx₀V)
  refine ⟨Y.basicOpen r, f₂', f₃', min ε ε₁, F, lt_min hε hε₁, ?_, ?_, hD⟩
  ·
    intro v hv
    apply hball v (Metric.ball_subset_ball (min_le_right _ _) hv)
  ·
    intro v h hv
    have hvε : v ∈ Metric.ball v₀ ε := Metric.ball_subset_ball (min_le_left _ _) hv
    have hU' : ⊤ ≤ (TopologicalSpace.Opens.map (π v).base).obj U := hU v hvε
    rw [hF v hU' hvε]
    have key : ∀ (fj : X.presheaf.obj (op U)) (fj' : Y.presheaf.obj (op (Y.basicOpen r))), g.app (Y.basicOpen r) fj' = X.presheaf.map (homOfLE hVU).op fj → ((π v ≫ g).appLE (Y.basicOpen r) ⊤ h) fj' = ((π v).appLE U ⊤ hU') fj := by
      intro fj fj'
      intro hfj
      rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, hfj, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rw [key f₁ f₂' hf₂', key f₂ f₃' hf₃']


-- created on 2026-10-20
