import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma ringHom_flat_mk_comp
  {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A : Type u} [CommRing A]
  (θ : RingHom O A)
  (J : Ideal A)
  -- given
  (hsat : ∀ (ϖ : O), Irreducible ϖ → ∀ s : A, θ ϖ * s ∈ J → s ∈ J) :
  -- imply
  ((Ideal.Quotient.mk J).comp θ).Flat := by
  -- proof
  classical
  let _ : Algebra O (A ⧸ J) := ((Ideal.Quotient.mk J).comp θ).toAlgebra
  show Module.Flat O (A ⧸ J)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hpow : ∀ (n : ℕ) (s : A), θ ϖ ^ n * s ∈ J → s ∈ J := by
    intro n
    induction n with
    | zero =>
      intro s hs
      simpa using hs
    | succ k ih =>
      intro s hs
      have h1 : θ ϖ ^ k * (θ ϖ * s) ∈ J := by
        rw [show θ ϖ ^ k * (θ ϖ * s) = θ ϖ ^ (k + 1) * s by ring]
        apply hs
      refine hsat ϖ hϖ s (ih _ h1)
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro m hm
  rw [Submodule.mem_torsion_iff] at hm
  obtain ⟨⟨a, ha⟩, ham⟩ := hm
  rw [Submodule.mem_bot]
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m
  have h1 : Ideal.Quotient.mk J (θ ((u : O) * ϖ ^ n) * s) = 0 := by
    rw [map_mul (Ideal.Quotient.mk J)]
    apply ham
  rw [Ideal.Quotient.eq_zero_iff_mem] at h1 ⊢
  have h2 : θ ϖ ^ n * s ∈ J := by
    have := J.mul_mem_left (θ (↑u⁻¹ : O)) h1
    rwa [← mul_assoc, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, map_pow] at this
  refine hpow n s h2

/--
[AlgebraicGeometry_IdealSheafData_flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IdealSheafData_flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing.lean)
-/
@[path]
private lemma main
  {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {X : (Scheme : Type (u + 1))}
  (q : X ⟶ Spec (CommRingCat.of O))
  (J : X.IdealSheafData)
  -- given
  (hsat : ∀ (ϖ : O), Irreducible ϖ → ∀ (U : X.affineOpens) (s : X.presheaf.obj (op (U : X.Opens))), X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) * s ∈ J.ideal U → s ∈ J.ideal U) :
  -- imply
  Flat (J.subschemeι ≫ q) := by
  -- proof
  classical
  rw [HasRingHomProperty.iff_of_source_openCover (P := @Flat) J.subschemeCover.openCover]
  intro U
  change X.affineOpens at U
  have hU : IsAffineOpen (U : X.Opens) := U.2
  set θ : RingHom O (X.presheaf.obj (op (U : X.Opens))) :=
    (q.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom with hθ
  have hmor : J.subschemeCover.openCover.f U ≫ J.subschemeι ≫ q =
    Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (J.ideal U)).comp θ)) := by
    show J.subschemeCover.f U ≫ J.subschemeι ≫ q = _
    rw [← Category.assoc, J.subschemeCover_map_subschemeι U]
    change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U))) ≫ hU.isoSpec.inv) ≫ (U : X.Opens).ι ≫ q = _
    rw [Category.assoc, hU.isoSpec_inv_ι_assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hU le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  rw [hmor]
  have key : ((Ideal.Quotient.mk (J.ideal U)).comp θ).Flat := by
    refine ringHom_flat_mk_comp θ (J.ideal U) (fun ϖ hϖ s hs => hsat ϖ hϖ U s ?_)
    have : θ ϖ = X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op
      (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) := by
      rw [hθ, RingHom.comp_apply]
      show (q.appLE ⊤ U le_top).hom _ = _
      rw [Scheme.Hom.appLE]
      rfl
    rw [← this]
    apply hs
  have := (HasRingHomProperty.Spec_iff (P := @Flat) (φ := CommRingCat.ofHom ((Ideal.Quotient.mk (J.ideal U)).comp θ))).mpr key
  apply HasRingHomProperty.appTop (P := @Flat) _ this


-- created on 2026-10-20
