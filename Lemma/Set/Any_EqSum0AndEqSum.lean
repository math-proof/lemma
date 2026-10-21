import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[RingHom_exists_eq_sum_mul_of_forall_sum_mul_eq_zero_of_forall_mem_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingHom_exists_eq_sum_mul_of_forall_sum_mul_eq_zero_of_forall_mem_range.lean)
-/
@[path]
private lemma main
  [Field k] [Field K]
  (φ : RingHom k K)
  {n : ℕ}
  (f : Fin n → X → K)
  (c : Fin n → K)
  -- given
  (hf : ∀ i x, f i x ∈ Set.range φ)
  (hc : ∀ x, ∑ i, c i * f i x = 0) :
  -- imply
  ∃ (m : ℕ) (d : Fin m → K) (v : Fin m → Fin n → k), (∀ j x, ∑ i, φ (v j i) * f i x = 0) ∧ ∀ i, c i = ∑ j, d j * φ (v j i) := by
  -- proof
  classical
  let _ : Algebra k K := φ.toAlgebra
  have hφ : ∀ a : k, φ a = algebraMap k K a := fun a => rfl
  choose g hg using hf
  let B := Module.Free.chooseBasis k K
  let S : Finset (Module.Free.ChooseBasisIndex k K) := Finset.univ.biUnion fun i => (B.repr (c i)).support
  let e : Fin S.card ≃ ↥S := S.equivFin.symm
  refine ⟨S.card, fun j => B (e j), fun j i => B.repr (c i) (e j), ?_, ?_⟩
  ·
    intro j x
    have h0 : ∑ i, (g i x) • c i = 0 := by
      rw [← hc x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, ← hφ, hg, mul_comm]
    have h1 := congrArg (fun y : K => B.repr y (e j)) h0
    simp only [map_sum, map_smul, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at h1
    have h2 := congrArg φ h1
    rw [map_sum, map_zero] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hg, mul_comm]
  ·
    intro i
    have hsupp : (B.repr (c i)).support ⊆ S := by
      intro α hα
      apply Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hα⟩
    calc
      _ = (B.repr (c i)).sum (fun α a => a • B α) := (B.linearCombination_repr (c i)).symm
      _ = ∑ α ∈ S, (B.repr (c i)) α • B α := by
        rw [Finsupp.sum]
        refine Finset.sum_subset hsupp fun α _ hα => ?_
        rw [Finsupp.notMem_support_iff.mp hα, zero_smul]
      _ = ∑ j : Fin S.card, (B.repr (c i)) (e j) • B (e j) := by
        rw [← Finset.sum_coe_sort S]
        apply (Equiv.sum_comp e (fun s : ↥S => (B.repr (c i)) s • B s)).symm
      _ = ∑ j, B (e j) * φ (B.repr (c i) (e j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.smul_def, ← hφ, mul_comm]


-- created on 2026-10-20
