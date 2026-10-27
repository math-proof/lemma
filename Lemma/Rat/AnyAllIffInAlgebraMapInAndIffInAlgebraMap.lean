import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[ValuationSubring_exists_forall_mem_iff_of_forall_eq_of_agree](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_exists_forall_mem_iff_of_forall_eq_of_agree.lean)
-/
@[path]
private lemma main
  [Field K₁] [Field K] [Field T] [Field F]
  [Algebra K₁ K] [Algebra K₁ T] [Algebra K F] [Algebra T F] [Algebra K₁ F]
  [IsScalarTower K₁ K F] [IsScalarTower K₁ T F]
  (A : ValuationSubring K) (V : ValuationSubring T)
  (hagree : ∀ x : K₁, algebraMap K₁ K x ∈ A ↔ algebraMap K₁ T x ∈ V)
  (hU : ∀ A' : ValuationSubring K, (∀ x : K₁, algebraMap K₁ K x ∈ A' ↔ algebraMap K₁ K x ∈ A) → A' = A) :
  -- imply
  ∃ O : ValuationSubring F, (∀ t : T, algebraMap T F t ∈ O ↔ t ∈ V) ∧ (∀ k : K, algebraMap K F k ∈ O ↔ k ∈ A) := by
  -- proof
  classical
  let Vloc : LocalSubring F := LocalSubring.map (algebraMap T F) V.toLocalSubring
  have hVloc : Vloc.toSubring = V.toSubring.map (algebraMap T F) := LocalSubring.map_toSubring _ _
  obtain ⟨O, hO⟩ := Vloc.exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := hO
  have hmemloc : ∀ v : T, v ∈ V → algebraMap T F v ∈ Vloc.toSubring := fun v hv => by
    rw [hVloc]
    refine Subring.mem_map.2 ⟨v, hv, rfl⟩
  have hVF : ∀ v : T, v ∈ V → algebraMap T F v ∈ O := fun v hv => hle (hmemloc v hv)
  have hunitV : ∀ (v : T) (hv : v ∈ V), IsUnit (⟨algebraMap T F v, hmemloc v hv⟩ : ↥Vloc.toSubring) →
      IsUnit (⟨v, hv⟩ : ↥V) := by
    intro v hv hu
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
    have hw2 : (w : F) ∈ V.toSubring.map (algebraMap T F) := by rw [← hVloc]; apply w.2
    obtain ⟨w', hw'V, hw'⟩ := Subring.mem_map.1 hw2
    refine isUnit_iff_exists_inv.2 ⟨⟨w', hw'V⟩, Subtype.ext ?_⟩
    apply (algebraMap T F).injective
    have h := congrArg Subtype.val hw
    change algebraMap T F v * (w : F) = 1 at h
    change algebraMap T F (v * w') = algebraMap T F 1
    rw [map_mul, map_one, hw']
    refine h
  have hT : ∀ t : T, algebraMap T F t ∈ O ↔ t ∈ V := by
    intro t
    refine ⟨fun ht => ?_, fun ht => hVF t ht⟩
    by_contra htV
    have ht0 : t ≠ 0 := fun h => htV (h ▸ V.zero_mem)
    have hinv : t⁻¹ ∈ V := (V.mem_or_inv_mem t).resolve_left htV
    have hnu : ¬ IsUnit (⟨t⁻¹, hinv⟩ : ↥V) := by
      intro hu
      apply htV
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
      have h := congrArg Subtype.val hw
      change t⁻¹ * (w : T) = 1 at h
      have : (w : T) = t := by
        rw [← mul_inv_cancel₀ (inv_ne_zero ht0)] at h
        have := mul_left_cancel₀ (inv_ne_zero ht0) h
        rw [this, inv_inv]
      rw [← this]
      apply w.2
    have hnuO : ¬ IsUnit (Subring.inclusion hle ⟨algebraMap T F t⁻¹, hmemloc _ hinv⟩) :=
      fun hu => hnu (hunitV _ hinv (IsLocalHom.map_nonunit _ hu))
    refine (hnuO ?_)
    refine isUnit_iff_exists_inv.2 ⟨⟨algebraMap T F t, ht⟩, Subtype.ext ?_⟩
    change algebraMap T F t⁻¹ * algebraMap T F t = 1
    rw [← map_mul, inv_mul_cancel₀ ht0, map_one]
  have hK : O.comap (algebraMap K F) = A := by
    apply hU
    intro x
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply K₁ K F,
      IsScalarTower.algebraMap_apply K₁ T F, hT, hagree]
  refine ⟨O, hT, fun k => ?_⟩
  rw [← ValuationSubring.mem_comap (A := O) (f := algebraMap K F), hK]


-- created on 2026-10-20
