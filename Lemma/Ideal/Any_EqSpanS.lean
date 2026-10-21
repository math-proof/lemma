import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Ideal_exists_map_mk_span_singleton_eq_span_of_not_mem_smul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_exists_map_mk_span_singleton_eq_span_of_not_mem_smul.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsLocalRing R]
  {n : ℕ} (g : Fin (n + 1) → R)
  (x : R) (hx : x ∈ Ideal.span (Set.range g))
  (hxm : x ∉ maximalIdeal R • Ideal.span (Set.range g)) :
  -- imply
  ∃ g' : Fin n → R ⧸ Ideal.span ({x} : Set R), (Ideal.span (Set.range g)).map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) = Ideal.span (Set.range g') := by
  -- proof
  classical
  set I : Ideal R := Ideal.span (Set.range g) with hI
  set mk := Ideal.Quotient.mk (Ideal.span ({x} : Set R)) with hmk
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hx
  have hunit : ∃ j, IsUnit (a j) := by
    by_contra hno
    push Not at hno
    apply hxm
    rw [← ha]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    refine Submodule.smul_mem_smul ((mem_maximalIdeal _).2 (hno i)) ?_
    refine Ideal.subset_span ?_
    refine ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := hunit
  obtain ⟨u, hu⟩ := hj
  have hsplit : a j * g j + ∑ i : Fin n, a (j.succAbove i) * g (j.succAbove i) = x := by
    rw [← ha, Fin.sum_univ_succAbove _ j]
  refine ⟨fun i => mk (g (j.succAbove i)), le_antisymm ?_ ?_⟩
  ·
    rw [Ideal.map_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    if hij : i = j then
      subst hij
      have hx0 : mk x = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
      have e1 : mk (a i) * mk (g i) = -(∑ k : Fin n, mk (a (i.succAbove k)) * mk (g (i.succAbove k))) := by
        have hmksum := congrArg mk hsplit
        rw [map_add, map_mul, map_sum, hx0] at hmksum
        simp [map_mul] at hmksum
        linear_combination hmksum
      have e2 : mk (g i) = mk (↑u⁻¹ : R) * -(∑ k : Fin n, mk (a (i.succAbove k)) * mk (g (i.succAbove k))) := by
        rw [← e1, ← mul_assoc, ← map_mul, ← hu, Units.inv_mul, map_one, one_mul]
      rw [e2]
      refine Ideal.mul_mem_left _ _ ((Ideal.neg_mem_iff _).2 (Ideal.sum_mem _ (fun k _ => ?_)))
      refine Ideal.mul_mem_left _ _ ?_
      refine Ideal.subset_span ?_
      refine ⟨k, rfl⟩
    else
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
      refine Ideal.subset_span ?_
      refine ⟨k, rfl⟩
  ·
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    refine Ideal.mem_map_of_mem _ ?_
    refine Ideal.subset_span ?_
    refine ⟨j.succAbove k, rfl⟩


-- created on 2026-10-20
