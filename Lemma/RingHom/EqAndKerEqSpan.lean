import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IsLocalRing_exists_ringHom_comp_algebraMap_eq_and_ker_eq_span_of_injective_of_finite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_ringHom_comp_algebraMap_eq_and_ker_eq_span_of_injective_of_finite.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsLocalRing A] [CommRing S] [Algebra A S]
  (t : S) [Module.Finite A (S ⧸ Ideal.span ({t} : Set S))]
  -- given
  (hinj : Function.Injective (algebraMap A (S ⧸ Ideal.span ({t} : Set S))))
  (hfib : ∀ s : S, ∃ a : A, s - algebraMap A S a ∈ Ideal.span ({t} : Set S) ⊔ (maximalIdeal A).map (algebraMap A S)) :
  -- imply
  ∃ χ : RingHom S A, (∀ a : A, χ (algebraMap A S a) = a) ∧ RingHom.ker χ = Ideal.span ({t} : Set S) := by
  -- proof
  classical
  set I : Ideal S := Ideal.span ({t} : Set S) with hI
  set π : RingHom S (S ⧸ I) := Ideal.Quotient.mk I with hπ
  have hφ : ∀ a : A, algebraMap A (S ⧸ I) a = π (algebraMap A S a) := fun a => rfl
  have hsurj : Function.Surjective (algebraMap A (S ⧸ I)) := by
    let N : Submodule A (S ⧸ I) := LinearMap.range (Algebra.linearMap A (S ⧸ I))
    have htop : (⊤ : Submodule A (S ⧸ I)) ≤ N ⊔ (maximalIdeal A) • (⊤ : Submodule A (S ⧸ I)) := by
      rintro m -
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m
      obtain ⟨a, ha⟩ := hfib s
      have h1 : π (s - algebraMap A S a) ∈ (maximalIdeal A).map (algebraMap A (S ⧸ I)) := by
        obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp ha
        rw [← huv, map_add, (Ideal.Quotient.eq_zero_iff_mem).mpr hu, zero_add]
        have : (maximalIdeal A).map (algebraMap A (S ⧸ I)) = ((maximalIdeal A).map (algebraMap A S)).map π := by
          rw [Ideal.map_map]
          rfl
        rw [this]
        apply Ideal.mem_map_of_mem _ hv
      rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map] at h1
      have h2 : π s = algebraMap A (S ⧸ I) a + π (s - algebraMap A S a) := by
        rw [hφ, ← map_add, add_sub_cancel]
      rw [h2]
      refine Submodule.add_mem_sup ⟨a, rfl⟩ h1
    have hN : (⊤ : Submodule A (S ⧸ I)) ≤ N :=
      Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
        (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) htop
    intro m
    obtain ⟨a, ha⟩ := hN (Submodule.mem_top : m ∈ ⊤)
    refine ⟨a, ha⟩
  let e : RingEquiv A (S ⧸ I) := RingEquiv.ofBijective (algebraMap A (S ⧸ I)) ⟨hinj, hsurj⟩
  refine ⟨e.symm.toRingHom.comp π, fun a => ?_, ?_⟩
  ·
    show e.symm (π (algebraMap A S a)) = a
    rw [← hφ]
    apply e.symm_apply_apply a
  ·
    ext x
    simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, map_eq_zero_iff _ e.symm.injective]
    apply Ideal.Quotient.eq_zero_iff_mem


-- created on 2026-10-20
