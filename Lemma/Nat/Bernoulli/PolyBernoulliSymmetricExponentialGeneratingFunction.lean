import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped BigOperators


namespace MetaMathlibExt

/--
[pbs_pair_hasSum_abs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/PolyBernoulliSymmetricExponentialGeneratingFunction.lean)
-/
@[path]
private lemma pbs_pair_hasSum_abs (j : ℕ) (x y : ℝ) :
  HasSum
    (fun p : ℕ × ℕ =>
      (j.factorial : ℝ) ^ 2 *
        (Nat.stirlingSecond (p.1 + 1) (j + 1) : ℝ) *
        (Nat.stirlingSecond (p.2 + 1) (j + 1) : ℝ) *
        (|x| ^ p.1 / p.1.factorial) * (|y| ^ p.2 / p.2.factorial))
    (Real.exp |x| * Real.exp |y| *
      ((Real.exp |x| - 1) * (Real.exp |y| - 1)) ^ j) := by
  let u : ℕ → ℝ := fun n =>
    (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) * (|x| ^ n / n.factorial)
  let v : ℕ → ℝ := fun k =>
    (Nat.stirlingSecond (k + 1) (j + 1) : ℝ) * (|y| ^ k / k.factorial)
  have hx := hasSum_stirlingSecond_succ_egf j |x|
  have hy := hasSum_stirlingSecond_succ_egf j |y|
  have huv : Summable (fun p : ℕ × ℕ => u p.1 * v p.2) :=
    hx.summable.mul_of_nonneg hy.summable (fun _ => by positivity) (fun _ => by positivity)
  have hprod := hx.mul hy huv
  have hscaled := hprod.mul_left ((j.factorial : ℝ) ^ 2)
  have hlimit :
    (j.factorial : ℝ) ^ 2 *
      ((Real.exp |x| * (Real.exp |x| - 1) ^ j / j.factorial) *
        (Real.exp |y| * (Real.exp |y| - 1) ^ j / j.factorial)) =
      Real.exp |x| * Real.exp |y| *
        ((Real.exp |x| - 1) * (Real.exp |y| - 1)) ^ j := by
    rw [mul_pow]
    field_simp
  rw [← hlimit]
  exact hscaled.congr_fun fun p => by
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pbs_pair_hasSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/PolyBernoulliSymmetricExponentialGeneratingFunction.lean)
-/
@[path]
private lemma pbs_pair_hasSum (j : ℕ) (x y : ℝ) :
  HasSum
    (fun p : ℕ × ℕ =>
      (j.factorial : ℝ) ^ 2 *
        (Nat.stirlingSecond (p.1 + 1) (j + 1) : ℝ) *
        (Nat.stirlingSecond (p.2 + 1) (j + 1) : ℝ) *
        (x ^ p.1 / p.1.factorial) * (y ^ p.2 / p.2.factorial))
    (Real.exp x * Real.exp y *
      ((Real.exp x - 1) * (Real.exp y - 1)) ^ j) := by
  let u : ℕ → ℝ := fun n =>
    (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) * (x ^ n / n.factorial)
  let v : ℕ → ℝ := fun k =>
    (Nat.stirlingSecond (k + 1) (j + 1) : ℝ) * (y ^ k / k.factorial)
  have hux : Summable fun n => ‖u n‖ := by
    apply (hasSum_stirlingSecond_succ_egf j |x|).summable.congr
    intro n
    dsimp [u]
    simp only [abs_mul, abs_div, abs_pow]
    have hs : 0 ≤ (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) := by positivity
    have hf : 0 ≤ (n.factorial : ℝ) := by positivity
    rw [abs_of_nonneg hs, abs_of_nonneg hf]
  have hvy : Summable fun k => ‖v k‖ := by
    apply (hasSum_stirlingSecond_succ_egf j |y|).summable.congr
    intro k
    dsimp [v]
    simp only [abs_mul, abs_div, abs_pow]
    have hs : 0 ≤ (Nat.stirlingSecond (k + 1) (j + 1) : ℝ) := by positivity
    have hf : 0 ≤ (k.factorial : ℝ) := by positivity
    rw [abs_of_nonneg hs, abs_of_nonneg hf]
  have hx := hasSum_stirlingSecond_succ_egf j x
  have hy := hasSum_stirlingSecond_succ_egf j y
  have huv : Summable (fun p : ℕ × ℕ => u p.1 * v p.2) :=
    summable_mul_of_summable_norm hux hvy
  have hscaled := (hx.mul hy huv).mul_left ((j.factorial : ℝ) ^ 2)
  have hlimit :
    (j.factorial : ℝ) ^ 2 *
      ((Real.exp x * (Real.exp x - 1) ^ j / j.factorial) *
        (Real.exp y * (Real.exp y - 1) ^ j / j.factorial)) =
      Real.exp x * Real.exp y *
        ((Real.exp x - 1) * (Real.exp y - 1)) ^ j := by
    rw [mul_pow]
    field_simp
  rw [← hlimit]
  exact hscaled.congr_fun fun p => by
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pbs_triple_summable_abs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/PolyBernoulliSymmetricExponentialGeneratingFunction.lean)
-/
@[path]
private lemma pbs_triple_summable_abs (x y : ℝ)
  (hxy : (Real.exp |x| - 1) * (Real.exp |y| - 1) < 1) :
  Summable fun p : ℕ × (ℕ × ℕ) =>
    (p.1.factorial : ℝ) ^ 2 *
      (Nat.stirlingSecond (p.2.1 + 1) (p.1 + 1) : ℝ) *
      (Nat.stirlingSecond (p.2.2 + 1) (p.1 + 1) : ℝ) *
      (|x| ^ p.2.1 / p.2.1.factorial) *
      (|y| ^ p.2.2 / p.2.2.factorial) := by
  let r := (Real.exp |x| - 1) * (Real.exp |y| - 1)
  have hr : 0 ≤ r := by
    dsimp [r]
    exact mul_nonneg (sub_nonneg.mpr (Real.one_le_exp (abs_nonneg x)))
      (sub_nonneg.mpr (Real.one_le_exp (abs_nonneg y)))
  have habs : |r| < 1 := by simpa only [abs_of_nonneg hr] using hxy
  apply (summable_prod_of_nonneg (fun _ => by positivity)).2
  constructor
  · intro j
    exact (pbs_pair_hasSum_abs j x y).summable
  · have hgeom :=
    (summable_geometric_of_abs_lt_one habs).mul_left (Real.exp |x| * Real.exp |y|)
    apply hgeom.congr
    intro j
    exact (pbs_pair_hasSum_abs j x y).tsum_eq.symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pbs_triple_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/PolyBernoulliSymmetricExponentialGeneratingFunction.lean)
-/
@[path]
private lemma pbs_triple_summable (x y : ℝ)
  (hxy : (Real.exp |x| - 1) * (Real.exp |y| - 1) < 1) :
  Summable fun p : ℕ × (ℕ × ℕ) =>
    (p.1.factorial : ℝ) ^ 2 *
      (Nat.stirlingSecond (p.2.1 + 1) (p.1 + 1) : ℝ) *
      (Nat.stirlingSecond (p.2.2 + 1) (p.1 + 1) : ℝ) *
      (x ^ p.2.1 / p.2.1.factorial) *
      (y ^ p.2.2 / p.2.2.factorial) := by
  apply (pbs_triple_summable_abs x y hxy).of_norm_bounded
  intro p
  rw [Real.norm_eq_abs]
  simp only [abs_mul, abs_pow, abs_div]
  have hj : 0 ≤ (p.1.factorial : ℝ) := by positivity
  have hn : 0 ≤ (p.2.1.factorial : ℝ) := by positivity
  have hk : 0 ≤ (p.2.2.factorial : ℝ) := by positivity
  have hsn : 0 ≤ (Nat.stirlingSecond (p.2.1 + 1) (p.1 + 1) : ℝ) := by positivity
  have hsk : 0 ≤ (Nat.stirlingSecond (p.2.2 + 1) (p.1 + 1) : ℝ) := by positivity
  rw [abs_of_nonneg hj, abs_of_nonneg hn, abs_of_nonneg hk,
    abs_of_nonneg hsn, abs_of_nonneg hsk]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pbs_tsum_stirling_product](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/PolyBernoulliSymmetricExponentialGeneratingFunction.lean)
-/
@[path]
private lemma pbs_tsum_stirling_product (n k : ℕ) :
  (∑' j : ℕ, (j.factorial : ℝ) ^ 2 *
    (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
    (Nat.stirlingSecond (k + 1) (j + 1) : ℝ)) =
    ∑ j ∈ Finset.range (min n k + 1), (j.factorial : ℝ) ^ 2 *
      (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
      (Nat.stirlingSecond (k + 1) (j + 1) : ℝ) := by
  apply tsum_eq_sum
  intro j hj
  have hmin : min n k < j := by
    simp only [Finset.mem_range, not_lt] at hj
    omega
  obtain hnk | hkn := le_total n k
  · rw [Nat.min_eq_left hnk] at hmin
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega : n + 1 < j + 1)]
    simp
  · rw [Nat.min_eq_right hkn] at hmin
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega : k + 1 < j + 1)]
    simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pbs_stirling_product_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/PolyBernoulliSymmetricExponentialGeneratingFunction.lean)
-/
@[path]
private lemma pbs_stirling_product_summable (n k : ℕ) :
  Summable fun j : ℕ => (j.factorial : ℝ) ^ 2 *
    (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
    (Nat.stirlingSecond (k + 1) (j + 1) : ℝ) := by
  apply summable_of_ne_finset_zero (s := Finset.range (min n k + 1))
  intro j hj
  have hmin : min n k < j := by
    simp only [Finset.mem_range, not_lt] at hj
    omega
  obtain hnk | hkn := le_total n k
  · rw [Nat.min_eq_left hnk] at hmin
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega : n + 1 < j + 1)]
    simp
  · rw [Nat.min_eq_right hkn] at hmin
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega : k + 1 < j + 1)]
    simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pbs_ratio_abs_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/PolyBernoulliSymmetricExponentialGeneratingFunction.lean)
-/
@[path]
private lemma pbs_ratio_abs_lt_one (x y : ℝ)
  (hxy : (Real.exp |x| - 1) * (Real.exp |y| - 1) < 1) :
  |(Real.exp x - 1) * (Real.exp y - 1)| < 1 := by
  let q := (Real.exp x - 1) * (Real.exp y - 1)
  let c := Real.exp x * Real.exp y
  have houter : Summable fun j : ℕ => c * q ^ j := by
    apply (pbs_triple_summable x y hxy).prod.congr
    intro j
    exact (pbs_pair_hasSum j x y).tsum_eq
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hq : Summable fun j : ℕ => q ^ j := by
    apply (houter.mul_left c⁻¹).congr
    intro j
    simp [hc]
  exact summable_geometric_iff_norm_lt_one.mp hq

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pbs_rearrange](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/PolyBernoulliSymmetricExponentialGeneratingFunction.lean)
-/
@[path]
private lemma pbs_rearrange (x y : ℝ)
  (hxy : (Real.exp |x| - 1) * (Real.exp |y| - 1) < 1) :
  (∑' n : ℕ, ∑' k : ℕ,
    (∑ j ∈ Finset.range (min n k + 1),
      (j.factorial : ℝ) ^ 2 * (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
        (Nat.stirlingSecond (k + 1) (j + 1) : ℝ)) *
      (x ^ n / n.factorial) * (y ^ k / k.factorial)) =
    Real.exp (x + y) *
      (1 - (Real.exp x - 1) * (Real.exp y - 1))⁻¹ := by
  let F : ℕ → ℕ × ℕ → ℝ := fun j p =>
    (j.factorial : ℝ) ^ 2 *
      (Nat.stirlingSecond (p.1 + 1) (j + 1) : ℝ) *
      (Nat.stirlingSecond (p.2 + 1) (j + 1) : ℝ) *
      (x ^ p.1 / p.1.factorial) * (y ^ p.2 / p.2.factorial)
  have hF : Summable (Function.uncurry F) := pbs_triple_summable x y hxy
  have hfiber : ∀ n k : ℕ,
    (∑ j ∈ Finset.range (min n k + 1),
      (j.factorial : ℝ) ^ 2 * (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
        (Nat.stirlingSecond (k + 1) (j + 1) : ℝ)) *
      (x ^ n / n.factorial) * (y ^ k / k.factorial) =
      ∑' j : ℕ, F j (n, k) := by
    intro n k
    let C : ℕ → ℝ := fun j =>
      (j.factorial : ℝ) ^ 2 * (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
        (Nat.stirlingSecond (k + 1) (j + 1) : ℝ)
    have hC : Summable C := pbs_stirling_product_summable n k
    calc
      (∑ j ∈ Finset.range (min n k + 1),
        (j.factorial : ℝ) ^ 2 * (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
          (Nat.stirlingSecond (k + 1) (j + 1) : ℝ)) *
        (x ^ n / n.factorial) * (y ^ k / k.factorial) =
        (∑' j : ℕ, C j) *
          ((x ^ n / n.factorial) * (y ^ k / k.factorial)) := by
            rw [pbs_tsum_stirling_product]
            ring
      _ = ∑' j : ℕ, C j *
        ((x ^ n / n.factorial) * (y ^ k / k.factorial)) :=
        (hC.tsum_mul_right _).symm
      _ = ∑' j : ℕ, F j (n, k) := by
        apply tsum_congr
        intro j
        dsimp [C, F]
        ring
  have hleft : Summable fun p : ℕ × ℕ => ∑' j : ℕ, F j p :=
    hF.prod_symm.prod
  have hratio := pbs_ratio_abs_lt_one x y hxy
  calc
    (∑' n : ℕ, ∑' k : ℕ,
      (∑ j ∈ Finset.range (min n k + 1),
        (j.factorial : ℝ) ^ 2 * (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
          (Nat.stirlingSecond (k + 1) (j + 1) : ℝ)) *
        (x ^ n / n.factorial) * (y ^ k / k.factorial)) =
      ∑' n : ℕ, ∑' k : ℕ, ∑' j : ℕ, F j (n, k) := by
        apply tsum_congr
        intro n
        apply tsum_congr
        intro k
        exact hfiber n k
    _ = ∑' p : ℕ × ℕ, ∑' j : ℕ, F j p := hleft.tsum_prod.symm
    _ = ∑' j : ℕ, ∑' p : ℕ × ℕ, F j p := hF.tsum_comm
    _ = ∑' j : ℕ,
      Real.exp x * Real.exp y *
        ((Real.exp x - 1) * (Real.exp y - 1)) ^ j := by
      apply tsum_congr
      intro j
      exact (pbs_pair_hasSum j x y).tsum_eq
    _ = Real.exp x * Real.exp y *
      (1 - (Real.exp x - 1) * (Real.exp y - 1))⁻¹ :=
      ((hasSum_geometric_of_abs_lt_one hratio).mul_left
        (Real.exp x * Real.exp y)).tsum_eq
    _ = Real.exp (x + y) *
      (1 - (Real.exp x - 1) * (Real.exp y - 1))⁻¹ := by
      rw [Real.exp_add]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pbs_denominator](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/PolyBernoulliSymmetricExponentialGeneratingFunction.lean)
-/
@[path]
private lemma pbs_denominator (x y : ℝ) :
  1 - (Real.exp x - 1) * (Real.exp y - 1) =
    Real.exp x + Real.exp y - Real.exp (x + y) := by
  rw [Real.exp_add]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[polyBernoulli_negative_symmetric_exponential_generating_function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/PolyBernoulliSymmetricExponentialGeneratingFunction.lean)
-/
@[path]
lemma polyBernoulli_negative_symmetric_exponential_generating_function
  {B : ℕ → ℕ → ℝ}
  {x y : ℝ}
-- given
  (hB : ∀ n k : ℕ, B n k = ∑ j ∈ Finset.range (min n k + 1), (j.factorial : ℝ) ^ 2 * Nat.stirlingSecond (n + 1) (j + 1) * Nat.stirlingSecond (k + 1) (j + 1))
  (hxy : (Real.exp |x| - 1) * (Real.exp |y| - 1) < 1) :
-- imply
  (∑' n : ℕ, ∑' k : ℕ,
    B n k * (x ^ n / n.factorial) * (y ^ k / k.factorial)) =
    Real.exp (x + y) /
    (Real.exp x + Real.exp y - Real.exp (x + y)) := by
-- proof
  calc
    (∑' n : ℕ, ∑' k : ℕ,
      B n k * (x ^ n / n.factorial) * (y ^ k / k.factorial)) =
      ∑' n : ℕ, ∑' k : ℕ,
        (∑ j ∈ Finset.range (min n k + 1),
          (j.factorial : ℝ) ^ 2 * (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
            (Nat.stirlingSecond (k + 1) (j + 1) : ℝ)) *
          (x ^ n / n.factorial) * (y ^ k / k.factorial) := by
            apply tsum_congr
            intro n
            apply tsum_congr
            intro k
            rw [hB n k]
    _ = Real.exp (x + y) *
      (1 - (Real.exp x - 1) * (Real.exp y - 1))⁻¹ :=
      pbs_rearrange x y hxy
    _ = Real.exp (x + y) /
      (Real.exp x + Real.exp y - Real.exp (x + y)) := by
      rw [div_eq_mul_inv, ← pbs_denominator]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
