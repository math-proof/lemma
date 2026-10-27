import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.Buildings.code.AffineCoxeter.PerronFrobeniusProof
open Finset BigOperators CoxeterGroup PerronFrobeniusProof


/--
[QF_eq_BF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma QF_eq_BF_eq
  [DecidableEq B]
  [Fintype B]
  {f : B → B → ℝ}
  {v : B → ℝ} :
-- imply
  QF f v = BF f v v := by
-- proof
  apply PerronFrobeniusProof.QF_eq_BF f v

/--
[BF_add_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma BF_add_left_eq
  [DecidableEq B]
  [Fintype B]
  {f : B → B → ℝ}
  {u v w : B → ℝ} :
-- imply
  BF f (fun b => u b + v b) w = BF f u w + BF f v w := by
-- proof
  apply PerronFrobeniusProof.BF_add_left f u v w

/--
[BF_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma BF_add_right_eq
  [DecidableEq B]
  [Fintype B]
  {f : B → B → ℝ}
  {u v w : B → ℝ} :
-- imply
  BF f u (fun b => v b + w b) = BF f u v + BF f u w := by
-- proof
  apply PerronFrobeniusProof.BF_add_right f u v w

/--
[BF_smul_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma BF_smul_left_eq
  [DecidableEq B]
  [Fintype B]
  {f : B → B → ℝ}
  {c : ℝ}
  {v w : B → ℝ} :
-- imply
  BF f (fun b => c * v b) w = c * BF f v w := by
-- proof
  apply PerronFrobeniusProof.BF_smul_left f c v w

/--
[BF_smul_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma BF_smul_right_eq
  [DecidableEq B]
  [Fintype B]
  {f : B → B → ℝ}
  {c : ℝ}
  {v w : B → ℝ} :
-- imply
  BF f v (fun b => c * w b) = c * BF f v w := by
-- proof
  apply PerronFrobeniusProof.BF_smul_right f c v w

/--
[QF_add_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma QF_add_smul_eq
  [DecidableEq B]
  [Fintype B]
  {f : B → B → ℝ}
  {v w : B → ℝ}
  {c : ℝ} :
-- imply
  QF f (fun b => v b + c * w b) = QF f v + c * (BF f v w + BF f w v) + c ^ 2 * QF f w := by
-- proof
  apply PerronFrobeniusProof.QF_add_smul f v w c

/--
[BF_left_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma BF_left_single_eq
  [DecidableEq B]
  [Fintype B]
  {f : B → B → ℝ}
  {v : B → ℝ}
  {i : B} :
-- imply
  BF f (Pi.single i 1) v = ∑ t, f i t * v t := by
-- proof
  apply PerronFrobeniusProof.BF_left_single f v i

/--
[BF_right_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma BF_right_single_eq
  [DecidableEq B]
  [Fintype B]
  {f : B → B → ℝ}
  {v : B → ℝ}
  {i : B} :
-- imply
  BF f v (Pi.single i 1) = ∑ s, v s * f s i := by
-- proof
  apply PerronFrobeniusProof.BF_right_single f v i

/--
[BF_sum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma BF_sum_eq_zero_eq
  [DecidableEq B]
  [Fintype B]
  {f : B → B → ℝ}
  {v w : B → ℝ}
-- given
  (hPSD : ∀ u : B → ℝ, QF f u ≥ 0)
  (hQv : QF f v = 0) :
-- imply
  BF f v w + BF f w v = 0 := by
-- proof
  apply PerronFrobeniusProof.BF_sum_eq_zero f v hPSD hQv w

/--
[combined_row_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma combined_row_sum_eq
  [DecidableEq B]
  [Fintype B]
  {f : B → B → ℝ}
  {v : B → ℝ}
  {i : B}
-- given
  (hBF_zero : ∀ w, BF f v w + BF f w v = 0) :
-- imply
  ∑ t, (f i t + f t i) * v t = 0 := by
-- proof
  apply PerronFrobeniusProof.combined_row_sum f v i hBF_zero

/--
[abs_sq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma abs_sq_mul_eq
  [DecidableEq B]
  [Fintype B]
  {a c : ℝ} :
-- imply
  |a| * c * |a| = a * c * a := by
-- proof
  apply PerronFrobeniusProof.abs_sq_mul a c

/--
[abs_mul_neg_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma abs_mul_neg_le_eq
  [DecidableEq B]
  [Fintype B]
  {a b c : ℝ}
-- given
  (hc : c ≤ 0) :
-- imply
  |a| * c * |b| ≤ a * c * b := by
-- proof
  apply PerronFrobeniusProof.abs_mul_neg_le a b c hc

/--
[QF_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma QF_abs_le_eq
  [DecidableEq B]
  [Fintype B]
  {f : B → B → ℝ}
  {v : B → ℝ}
-- given
  (hOffDiag : ∀ s t, s ≠ t → f s t ≤ 0) :
-- imply
  QF f (fun b => |v b|) ≤ QF f v := by
-- proof
  apply PerronFrobeniusProof.QF_abs_le f v hOffDiag

/--
[sum_eq_zero_of_nonpos'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma sum_eq_zero_of_nonpos'_eq
  [DecidableEq B]
  [Fintype B]
  {s : Finset ι}
  {g : ι → ℝ}
-- given
  (h_nonpos : ∀ i ∈ s, g i ≤ 0)
  (h_sum : ∑ i ∈ s, g i = 0) :
-- imply
  ∀ i ∈ s, g i = 0 := by
-- proof
  apply PerronFrobeniusProof.sum_eq_zero_of_nonpos' h_nonpos h_sum

/--
[offdiag_zero_from_row](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma offdiag_zero_from_row_eq
  [DecidableEq B]
  [Fintype B]
  {f : B → B → ℝ}
  {v : B → ℝ}
  {i j : B}
-- given
  (hij : i ≠ j)
  (hv_nonneg : ∀ b, v b ≥ 0)
  (hvi : v i = 0)
  (hvj : v j > 0)
  (hOffDiag : ∀ s t, s ≠ t → f s t ≤ 0)
  (hrow : ∑ t, (f i t + f t i) * v t = 0) :
-- imply
  f i j = 0 ∧ f j i = 0 := by
-- proof
  apply PerronFrobeniusProof.offdiag_zero_from_row f v i j hij hv_nonneg hvi hvj hOffDiag hrow

/--
[nonneg_kernel_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma nonneg_kernel_pos_eq
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {f : B → B → ℝ}
  {v : B → ℝ}

-- given
  (hPSD : ∀ u : B → ℝ, QF f u ≥ 0)
  (hQv : QF f v = 0)
  (hv_nonneg : ∀ b, v b ≥ 0)
  (hv_ne : v ≠ 0)
  (hOffDiag : ∀ s t, s ≠ t → f s t ≤ 0)
  (hIndecomp : FormIndecomposable f) :
-- imply
  ∀ b, v b > 0 := by
-- proof
  apply PerronFrobeniusProof.nonneg_kernel_pos f v hPSD hQv hv_nonneg hv_ne hOffDiag hIndecomp

/--
[positive_kernel_proportional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma positive_kernel_proportional_eq
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {f : B → B → ℝ}
  {v w : B → ℝ}

-- given
  (hPSD : ∀ u : B → ℝ, QF f u ≥ 0)
  (hQv : QF f v = 0)
  (hQw : QF f w = 0)
  (hv_pos : ∀ b, v b > 0)
  (hw_pos : ∀ b, w b > 0)
  (hOffDiag : ∀ s t, s ≠ t → f s t ≤ 0)
  (hIndecomp : FormIndecomposable f) :
-- imply
  ∃ c : ℝ, w = fun b => c * v b := by
-- proof
  apply PerronFrobeniusProof.positive_kernel_proportional f v w hPSD hQv hQw hv_pos hw_pos hOffDiag hIndecomp

/--
[kernel_scalar_multiple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean)
-/
@[path]
private lemma kernel_scalar_multiple_eq
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {f : B → B → ℝ}
  {v w : B → ℝ}

-- given
  (hPSD : ∀ u : B → ℝ, QF f u ≥ 0)
  (hv_pos : ∀ b, v b > 0)
  (hQv : QF f v = 0)
  (hQw : QF f w = 0)
  (hOffDiag : ∀ s t, s ≠ t → f s t ≤ 0)
  (hIndecomp : FormIndecomposable f) :
-- imply
  ∃ c : ℝ, w = fun b => c * v b := by
-- proof
  apply PerronFrobeniusProof.kernel_scalar_multiple f v w hPSD hv_pos hQv hQw hOffDiag hIndecomp


-- created on 2026-10-23
