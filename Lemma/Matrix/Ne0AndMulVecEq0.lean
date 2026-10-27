import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma helper_main
  [Field k] [Field K] [Algebra k K]
  [Fintype ι] [DecidableEq ι]
  (A : J → Matrix ι ι k)
  (v : ι → K)
  -- given
  (hv : v ≠ 0)
  (hAv : ∀ j, ((A j).map (algebraMap k K)).mulVec v = 0) :
  -- imply
  ∃ w : ι → k, w ≠ 0 ∧ ∀ j, (A j).mulVec w = 0 := by
  -- proof
  classical
  let b := Module.Free.chooseBasis k K
  obtain ⟨y₀, hy₀⟩ : ∃ y, v y ≠ 0 := by
    by_contra h
    push Not at h
    apply hv (funext h)
  have hrepr : b.repr (v y₀) ≠ 0 := by
    intro h
    apply hy₀ (b.repr.map_eq_zero_iff.mp h)
  obtain ⟨t, ht⟩ : ∃ t, b.repr (v y₀) t ≠ 0 := by
    by_contra h
    push Not at h
    apply hrepr (Finsupp.ext h)
  refine ⟨fun y => b.repr (v y) t, fun h => ht (by simpa using congrFun h y₀), fun j => ?_⟩
  funext x
  have hx := congrFun (hAv j) x
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hx ⊢
  have : b.repr (∑ y, (algebraMap k K) (A j x y) * v y) t = ∑ y, A j x y * b.repr (v y) t := by
    rw [map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [← this, hx, map_zero, Finsupp.zero_apply]

/--
[Matrix_exists_ne_zero_forall_mulVec_eq_zero_of_forall_map_mulVec_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_exists_ne_zero_forall_mulVec_eq_zero_of_forall_map_mulVec_eq_zero.lean)
-/
@[path]
private lemma main
  [Field k] [Field K] [Algebra k K]
  [Fintype ι] [DecidableEq ι]
  (A : J → Matrix ι ι k)
  (v : ι → K)
  -- given
  (hv : v ≠ 0)
  (hAv : ∀ j, ((A j).map (algebraMap k K)).mulVec v = 0) :
  -- imply
  ∃ w : ι → k, w ≠ 0 ∧ ∀ j, (A j).mulVec w = 0 :=
  helper_main A v hv hAv


-- created on 2026-10-20
