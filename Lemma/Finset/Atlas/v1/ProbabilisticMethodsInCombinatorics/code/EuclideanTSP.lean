import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.EuclideanTSP
open EuclideanTSP
open scoped Classical


namespace EuclideanTSP

/--
[tourLength_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/EuclideanTSP.lean)
-/
@[path]
lemma tourLength_nonneg
  {n : ℕ}
  [NeZero n]
  {x : Fin n → E2}
  {σ : Equiv.Perm (Fin n)} :
-- imply
  0 ≤ tourLength x σ :=
-- proof
  Finset.sum_nonneg fun _ _ => dist_nonneg

end EuclideanTSP

namespace EuclideanTSP

/--
[shortestTour_le_tourLength](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/EuclideanTSP.lean)
-/
@[path]
lemma shortestTour_le_tourLength
  {n : ℕ}
  [NeZero n]
  {x : Fin n → E2}
  {σ : Equiv.Perm (Fin n)} :
-- imply
  shortestTour x ≤ tourLength x σ :=
-- proof
  ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ tourLength_nonneg x _⟩ σ

end EuclideanTSP

namespace EuclideanTSP

/--
[shortestTour_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/EuclideanTSP.lean)
-/
@[path]
lemma shortestTour_nonneg
  {n : ℕ}
  [NeZero n]
  {x : Fin n → E2} :
-- imply
  0 ≤ shortestTour x :=
-- proof
  le_ciInf fun σ => tourLength_nonneg x σ

end EuclideanTSP

namespace EuclideanTSP

/--
[cert_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/EuclideanTSP.lean)
-/
@[path]
lemma cert_nonneg
  {n : ℕ}
  [NeZero n]
  {x : Fin n → E2}
  {σ : Equiv.Perm (Fin n)}
  {i : Fin n} :
-- imply
  0 ≤ cert x σ i := by
-- proof
  unfold cert; positivity

end EuclideanTSP

namespace EuclideanTSP

/--
[sum_dist_succ_eq_tourLength](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/EuclideanTSP.lean)
-/
@[path]
lemma sum_dist_succ_eq_tourLength
  {n : ℕ}
  [NeZero n]
  {x : Fin n → E2}
  {σ : Equiv.Perm (Fin n)} :
-- imply
  ∑ i : Fin n, dist (x i) (x (σ (σ.symm i + 1))) = tourLength x σ := by
-- proof
  unfold tourLength
  exact Finset.sum_equiv σ.symm (fun _ => by simp) (fun i _ => by simp [Equiv.apply_symm_apply])

end EuclideanTSP

namespace EuclideanTSP

/--
[sum_dist_pred_eq_tourLength](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/EuclideanTSP.lean)
-/
@[path]
lemma sum_dist_pred_eq_tourLength
  {n : ℕ}
  [NeZero n]
  {x : Fin n → E2}
  {σ : Equiv.Perm (Fin n)} :
-- imply
  ∑ i : Fin n, dist (x i) (x (σ (σ.symm i - 1))) = tourLength x σ := by
-- proof
  unfold tourLength
  calc ∑ i, dist (x i) (x (σ (σ.symm i - 1)))
    = ∑ j, dist (x (σ j)) (x (σ (j - 1))) :=
      Finset.sum_equiv σ.symm (fun _ => by simp) (fun i _ => by simp [Equiv.apply_symm_apply])
    _ = ∑ j, dist (x (σ (j - 1))) (x (σ j)) := by congr 1; ext j; exact dist_comm _ _
    _ = ∑ k, dist (x (σ k)) (x (σ (k + 1))) := by
      refine Finset.sum_equiv (Equiv.addRight (-1 : Fin n)) (fun _ => by simp) (fun j _ => ?_)
      rw [show (Equiv.addRight (-1 : Fin n)) j = j - 1 from
        show j + (-1) = j - 1 from (sub_eq_add_neg j 1).symm, sub_add_cancel]

end EuclideanTSP

namespace EuclideanTSP

/--
[sum_cert_eq_four_mul_tourLength](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/EuclideanTSP.lean)
-/
@[path]
lemma sum_cert_eq_four_mul_tourLength
  {n : ℕ}
  [NeZero n]
  {x : Fin n → E2}
  {σ : Equiv.Perm (Fin n)} :
-- imply
  ∑ i : Fin n, cert x σ i = 4 * tourLength x σ := by
-- proof
  simp only [cert, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_dist_succ_eq_tourLength, sum_dist_pred_eq_tourLength]
  ring

end EuclideanTSP

namespace EuclideanTSP

/--
[tourLength_le_sum_cert](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/EuclideanTSP.lean)
-/
@[path]
lemma tourLength_le_sum_cert
  {n : ℕ}
  [NeZero n]
  {x : Fin n → E2}
  {σ : Equiv.Perm (Fin n)} :
-- imply
  tourLength x σ ≤ ∑ i : Fin n, cert x σ i := by
-- proof
  rw [sum_cert_eq_four_mul_tourLength]; linarith [tourLength_nonneg x σ]

end EuclideanTSP

namespace EuclideanTSP

/--
[cyclicSucc_eq_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/EuclideanTSP.lean)
-/
@[path]
lemma cyclicSucc_eq_add_one
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  [NeZero m]
  {i : Fin m} :
-- imply
  SpaceFillingCurve.cyclicSucc i = i + 1 := by
-- proof
  ext; simp [SpaceFillingCurve.cyclicSucc, Fin.val_add]

end EuclideanTSP

namespace EuclideanTSP

/--
[space_filling_curve_heuristic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/EuclideanTSP.lean)
-/
@[path]
lemma space_filling_curve_heuristic
  {n : ℕ}
  [NeZero n] :
-- imply
  ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) [NeZero m] (x : Fin m → E2), AllInUnitSquare x → ∃ σ : Equiv.Perm (Fin m), ∑ i : Fin m, dist (x (σ i)) (x (σ (i + 1))) ^ 2 ≤ C := by
-- proof
  obtain ⟨C, hC⟩ := SpaceFillingCurve.space_filling_curve_heuristic
  refine ⟨max C 1, by positivity, fun m _ x hx => ?_⟩
  have hx' : ∀ i, x i ∈ SpaceFillingCurve.unitSquare := by
    intro i j
    exact Set.mem_Icc.mpr (hx i j)
  obtain ⟨σ, hσ⟩ := hC m x hx'
  refine ⟨σ, ?_⟩
  have heq : ∀ i : Fin m, dist (x (σ i)) (x (σ (i + 1))) ^ 2 =
    ‖x (σ i) - x (σ (SpaceFillingCurve.cyclicSucc i))‖ ^ 2 := by
    intro i
    rw [← cyclicSucc_eq_add_one, dist_eq_norm]
  simp_rw [heq]
  linarith [le_max_left C 1]

end EuclideanTSP

namespace EuclideanTSP

/--
[sum_sq_cert_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/EuclideanTSP.lean)
-/
@[path]
lemma sum_sq_cert_le
  {n : ℕ}
  [NeZero n]
  {C : ℝ}
  {x : Fin n → E2}
  {σ : Equiv.Perm (Fin n)}
-- given
  (hσ : ∑ i : Fin n, dist (x (σ i)) (x (σ (i + 1))) ^ 2 ≤ C) :
-- imply
  ∑ i : Fin n, (cert x σ i) ^ 2 ≤ 16 * C := by
-- proof
  have key : ∀ i : Fin n, (cert x σ i) ^ 2 ≤
    8 * (dist (x i) (x (σ (σ.symm i + 1))) ^ 2 +
      dist (x i) (x (σ (σ.symm i - 1))) ^ 2) := by
    intro i
    unfold cert
    nlinarith [sq_nonneg (dist (x i) (x (σ (σ.symm i + 1))) -
      dist (x i) (x (σ (σ.symm i - 1))))]
  have sum_succ : ∑ i : Fin n, dist (x i) (x (σ (σ.symm i + 1))) ^ 2 =
    ∑ j : Fin n, dist (x (σ j)) (x (σ (j + 1))) ^ 2 :=
    Finset.sum_equiv σ.symm (fun _ => by simp) (fun i _ => by simp [Equiv.apply_symm_apply])
  have sum_pred : ∑ i : Fin n, dist (x i) (x (σ (σ.symm i - 1))) ^ 2 =
    ∑ j : Fin n, dist (x (σ j)) (x (σ (j + 1))) ^ 2 := by
    calc ∑ i, dist (x i) (x (σ (σ.symm i - 1))) ^ 2
      = ∑ j, dist (x (σ j)) (x (σ (j - 1))) ^ 2 :=
        Finset.sum_equiv σ.symm (fun _ => by simp) (fun i _ => by simp [Equiv.apply_symm_apply])
      _ = ∑ j, dist (x (σ (j - 1))) (x (σ j)) ^ 2 := by
        congr 1; ext j; rw [dist_comm]
      _ = ∑ k, dist (x (σ k)) (x (σ (k + 1))) ^ 2 := by
        refine Finset.sum_equiv (Equiv.addRight (-1 : Fin n)) (fun _ => by simp) (fun j _ => ?_)
        rw [show (Equiv.addRight (-1 : Fin n)) j = j - 1 from
          show j + (-1) = j - 1 from (sub_eq_add_neg j 1).symm, sub_add_cancel]
  calc ∑ i : Fin n, (cert x σ i) ^ 2
    ≤ ∑ i, 8 * (dist (x i) (x (σ (σ.symm i + 1))) ^ 2 +
      dist (x i) (x (σ (σ.symm i - 1))) ^ 2) :=
      Finset.sum_le_sum fun i _ => key i
    _ = 8 * ((∑ i, dist (x i) (x (σ (σ.symm i + 1))) ^ 2) +
      (∑ i, dist (x i) (x (σ (σ.symm i - 1))) ^ 2)) := by
      simp [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    _ = 16 * ∑ j, dist (x (σ j)) (x (σ (j + 1))) ^ 2 := by
      rw [sum_succ, sum_pred]; ring
    _ ≤ 16 * C := by linarith
/-- Theorem 9.6.1 / 9.6.3 (Rhee–Talagrand TSP concentration, certificate form). For every
configuration $x$ in the unit square, there exist non-negative weights $\alpha_i$ such
that the shortest tour is `1`-Lipschitz with respect to changes on a subset of indices
bounded by $\sum_{i : x_i \ne y_i} \alpha_i$, and the weights satisfy $\sum_i \alpha_i^2 \le C$
for a universal constant $C$. -/

end EuclideanTSP


-- created on 2026-10-23
