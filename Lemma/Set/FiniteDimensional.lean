import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma isIntegral_apply
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
  [CommRing A] [CommRing K] [Algebra A K]
  (χ' : RingHom S K)
  (s : S)
  -- given
  (h : ∀ r : R, χ' (algebraMap R S r) ∈ (algebraMap A K).range) :
  -- imply
  IsIntegral A (χ' s) := by
  -- proof
  classical
  nontriviality K
  obtain ⟨p, hpm, hps⟩ := Algebra.IsIntegral.isIntegral (R := R) s
  set χ : RingHom R K := χ'.comp (algebraMap R S) with hχ
  have hlift : p.map χ ∈ Polynomial.lifts (algebraMap A K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    obtain ⟨a, ha⟩ := h (p.coeff n)
    refine ⟨a, ha⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift (hpm.map χ)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, Polynomial.eval_map, ← Polynomial.hom_eval₂, hps, map_zero]

/--
[RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
  [Field E] [Field K] [Algebra E K]
  (χ' : RingHom S K)
  -- given
  (h : ∀ r : R, χ' (algebraMap R S r) ∈ (algebraMap E K).range) :
  -- imply
  FiniteDimensional E (IntermediateField.adjoin E (Set.range χ')) := by
  -- proof
  classical
  obtain ⟨t, ht⟩ := Module.finite_def.mp (inferInstance : Module.Finite R S)
  have hint : ∀ x ∈ (χ' '' (t : Set S)), IsIntegral E x := by
    rintro _ ⟨s, -, rfl⟩
    apply isIntegral_apply χ' s h
  have hsub : Set.range χ' ⊆ IntermediateField.adjoin E (χ' '' (t : Set S)) := by
    rintro _ ⟨s, rfl⟩
    have hs : s ∈ Submodule.span R (t : Set S) := by
      rw [ht]
      apply Submodule.mem_top
    induction hs using Submodule.span_induction with
    | mem x hx =>
      apply IntermediateField.subset_adjoin
      refine ⟨x, hx, rfl⟩
    | zero =>
      rw [map_zero]
      apply zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      apply add_mem hx hy
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul]
      obtain ⟨a, ha⟩ := h r
      rw [← ha]
      apply mul_mem (IntermediateField.algebraMap_mem _ a) hx
  have heq : IntermediateField.adjoin E (Set.range χ') = IntermediateField.adjoin E (χ' '' (t : Set S)) := by
    apply le_antisymm (IntermediateField.adjoin_le_iff.mpr hsub)
    apply IntermediateField.adjoin.mono _ _ _
    ·
      rintro _ ⟨s, -, rfl⟩
      refine ⟨s, rfl⟩
  rw [heq]
  let _ : Finite (χ' '' (t : Set S)) := Set.toFinite _
  apply IntermediateField.finiteDimensional_adjoin hint


-- created on 2026-10-20
