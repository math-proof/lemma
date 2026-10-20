import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false


/--
[AlgebraicGeometry_exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal.lean)
-/
@[path]
private lemma main
  {B₁ B₀ : Type} [CommRing B₁] [IsLocalRing B₁] [CommRing B₀]
  (π : RingHom B₁ B₀) (hπ : Function.Surjective π) (hI : RingHom.ker π ≤ maximalIdeal B₁)
  {X X₀ : (Scheme : Type 1)} (f : X ⟶ Spec (CommRingCat.of B₁)) (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (g : X₀ ⟶ X)
  (hg : g ≫ f = f₀ ≫ Spec.map (CommRingCat.ofHom π))
  (h₁ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appTop).hom)
  (h₀ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of B₀)).inv ≫ f₀.appTop).hom)
  (s : X₀.presheaf.obj (Opposite.op (⊤ : X₀.Opens))) (hs : IsUnit s) :
  -- imply
  ∃ u : X.presheaf.obj (Opposite.op (⊤ : X.Opens)), IsUnit u ∧ g.appTop.hom u = s := by
  -- proof
  classical
  have hnat : ∀ c : B₁, g.appTop.hom (((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appTop).hom c) = ((Scheme.ΓSpecIso (CommRingCat.of B₀)).inv ≫ f₀.appTop).hom (π c) := by
    intro c
    have hN := congrArg (fun k => (k.hom) c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom π))
    have hC := congrArg (fun k => (k.hom) ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv.hom c)) (show f.appTop ≫ g.appTop = (Spec.map (CommRingCat.ofHom π)).appTop ≫ f₀.appTop by rw [← Scheme.Hom.comp_appTop, hg, Scheme.Hom.comp_appTop])
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hN hC ⊢
    rw [hC, ← hN]
    rfl
  let e₀ := RingEquiv.ofBijective ((Scheme.ΓSpecIso (CommRingCat.of B₀)).inv ≫ f₀.appTop).hom h₀
  obtain ⟨c₀, hc₀⟩ := h₀.2 s
  have hc₀u : IsUnit c₀ := by
    have h' : e₀.symm s = c₀ := e₀.injective ((by rw [RingEquiv.apply_symm_apply] : e₀ (e₀.symm s) = s).trans hc₀.symm)
    refine h' ▸ hs.map e₀.symm
  obtain ⟨c, rfl⟩ := hπ c₀
  have hcu : IsUnit c := by
    by_contra hcu
    have hcm : c ∈ maximalIdeal B₁ := (mem_maximalIdeal c).mpr (mem_nonunits_iff.mpr hcu)
    obtain ⟨d₀, hd₀⟩ := hc₀u.exists_right_inv
    obtain ⟨d, rfl⟩ := hπ d₀
    have hk : c * d - 1 ∈ RingHom.ker π := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_one, hd₀, sub_self]
    have h1 : (1 : B₁) ∈ maximalIdeal B₁ := by
      have := Ideal.sub_mem _ (Ideal.mul_mem_right d _ hcm) (hI hk)
      rwa [sub_sub_cancel] at this
    refine (maximalIdeal.isMaximal B₁).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  refine ⟨((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appTop).hom c, hcu.map _, by rw [hnat, hc₀]⟩


-- created on 2026-10-20
