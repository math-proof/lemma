import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.Ramanujan.Part1Ch2
open Real Filter Topology intervalIntegral
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry3InfiniteEvaluation


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry3InfiniteEvaluation

/--
[arctan_err](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2.lean)
-/
@[path]
`t ^ 3 - t + arctan t` is monotone on `[0, ∞)` (its derivative is nonnegative). -/
private lemma arctan_err (x : ℝ) (hx : 0 ≤ x) : x - arctan x ≤ x ^ 3 := by
  have hd : ∀ y : ℝ, HasDerivAt (fun t => t ^ 3 - t + arctan t) (3 * y ^ 2 - 1 + 1 / (1 + y ^ 2))
    y := by
    intro y
    have h1 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * y ^ 2) y := by
      simpa using hasDerivAt_pow 3 y
    have h2 : HasDerivAt (fun t : ℝ => t) 1 y := hasDerivAt_id y
    have h3 : HasDerivAt arctan (1 / (1 + y ^ 2)) y := hasDerivAt_arctan y
    exact (h1.sub h2).add h3
  have hmono : MonotoneOn (fun t => t ^ 3 - t + arctan t) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · exact fun z _ => (hd z).differentiableAt.differentiableWithinAt
    · intro z _
      rw [(hd z).deriv]
      have heq : 3 * z ^ 2 - 1 + 1 / (1 + z ^ 2) = (3 * z ^ 4 + 2 * z ^ 2) / (1 + z ^ 2) := by
        field_simp; ring
      rw [heq]; positivity
  have h0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by simp
  have := hmono h0 hx hx
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, arctan_zero,
    sub_zero, add_zero] at this
  linarith

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry3InfiniteEvaluation

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry3InfiniteEvaluation

/--
[partial_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2.lean)
-/
@[path]
identity `Entry3.ramanujan_part1_ch2_entry3_general`. -/
private lemma partial_sum (N : ℕ) :
  ∑ n ∈ Finset.range N, f n = (∑ k ∈ Finset.Ico (N + 1) (3 * N + 2), g k) - π / 4 := by
  have hl : ∑ k ∈ Finset.Icc 1 (2 * N + 1), arctan (1 / ((N : ℝ) + k)) =
    ∑ k ∈ Finset.Ico (N + 1) (3 * N + 2), g k := by
    have h := Finset.sum_Ico_add' g 1 (2 * N + 1 + 1) N
    rw [show 1 + N = N + 1 by omega, show 2 * N + 1 + 1 + N = 3 * N + 2 by omega,
      Finset.Ico_add_one_right_eq_Icc] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [g, Nat.cast_add, add_comm]
  have hr : ∑ k ∈ Finset.Icc 1 N,
    arctan (10 * (k : ℝ) / ((3 * (k : ℝ) ^ 2 + 2) * (9 * (k : ℝ) ^ 2 - 1))) =
    ∑ n ∈ Finset.range N, f n := by
    have h := Finset.sum_Ico_add'
      (fun k : ℕ => arctan (10 * (k : ℝ) / ((3 * (k : ℝ) ^ 2 + 2) * (9 * (k : ℝ) ^ 2 - 1)))) 0 N 1
    rw [zero_add, Finset.Ico_add_one_right_eq_Icc] at h
    rw [← h, Finset.range_eq_Ico]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [f, Nat.cast_add, Nat.cast_one]
  rw [← hl, ← hr, Entry3.ramanujan_part1_ch2_entry3_general N]
  ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry3InfiniteEvaluation

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry3InfiniteEvaluation

/--
[W_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2.lean)
-/
@[path]
private lemma W_tendsto :
  Tendsto (fun N : ℕ => ∑ k ∈ Finset.Ico (N + 1) (3 * N + 2), ((k : ℝ))⁻¹) atTop
    (𝓝 (Real.log 3)) := by
  have anti : ∀ a b : ℝ, 0 < a → AntitoneOn (fun x : ℝ => x⁻¹) (Set.Icc a b) := by
    intro a b ha x hx y hy hxy
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    simp only; gcongr
  have reindex : ∀ N : ℕ, ∑ i ∈ Finset.Ico N (3 * N + 1), ((↑(i + 1) : ℝ))⁻¹
    = ∑ k ∈ Finset.Ico (N + 1) (3 * N + 2), ((k : ℝ))⁻¹ := by
    intro N
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr (by congr 1; omega); intro i _; congr 2; omega
  have hlow : ∀ N : ℕ, Real.log ((3 * (N : ℝ) + 2) / ((N : ℝ) + 1))
    ≤ ∑ k ∈ Finset.Ico (N + 1) (3 * N + 2), ((k : ℝ))⁻¹ := by
    intro N
    have hanti : AntitoneOn (fun x : ℝ => x⁻¹) (Set.Icc ((N + 1 : ℕ) : ℝ) ((3 * N + 2 : ℕ) : ℝ)) :=
      anti _ _ (by exact_mod_cast Nat.succ_pos N)
    have h := AntitoneOn.integral_le_sum_Ico (a := N + 1) (b := 3 * N + 2) (f := fun x => x⁻¹)
      (by omega) hanti
    rw [integral_inv_of_pos (by positivity) (by positivity)] at h
    have hcast : Real.log ((((3 * N + 2 : ℕ) : ℝ)) / (((N + 1 : ℕ) : ℝ)))
      = Real.log ((3 * (N : ℝ) + 2) / ((N : ℝ) + 1)) := by push_cast; ring_nf
    rwa [hcast] at h
  have hup : ∀ N : ℕ, 1 ≤ N → (∑ k ∈ Finset.Ico (N + 1) (3 * N + 2), ((k : ℝ))⁻¹)
    ≤ Real.log ((3 * (N : ℝ) + 1) / (N : ℝ)) := by
    intro N hN
    have hanti : AntitoneOn (fun x : ℝ => x⁻¹) (Set.Icc ((N : ℕ) : ℝ) ((3 * N + 1 : ℕ) : ℝ)) :=
      anti _ _ (by exact_mod_cast hN)
    have h := AntitoneOn.sum_le_integral_Ico (a := N) (b := 3 * N + 1) (f := fun x => x⁻¹)
      (by omega) hanti
    rw [reindex N, integral_inv_of_pos (by exact_mod_cast hN) (by positivity)] at h
    have hcast : Real.log ((((3 * N + 1 : ℕ) : ℝ)) / ((N : ℕ) : ℝ))
      = Real.log ((3 * (N : ℝ) + 1) / (N : ℝ)) := by push_cast; ring_nf
    rwa [hcast] at h
  have hr1 : Tendsto (fun N : ℕ => Real.log ((3 * (N : ℝ) + 2) / ((N : ℝ) + 1))) atTop
    (𝓝 (Real.log 3)) := by
    have hratio : Tendsto (fun N : ℕ => (3 * (N : ℝ) + 2) / ((N : ℝ) + 1)) atTop (𝓝 3) := by
      have heq : ∀ N : ℕ, (3 * (N : ℝ) + 2) / ((N : ℝ) + 1) = 3 - 1 / ((N : ℝ) + 1) := by
        intro N
        have : ((N : ℝ) + 1) ≠ 0 := by positivity
        field_simp; ring
      rw [tendsto_congr heq]
      simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact (Real.continuousAt_log (by norm_num)).tendsto.comp hratio
  have hr2 : Tendsto (fun N : ℕ => Real.log ((3 * (N : ℝ) + 1) / (N : ℝ))) atTop
    (𝓝 (Real.log 3)) := by
    have hratio : Tendsto (fun N : ℕ => (3 * (N : ℝ) + 1) / (N : ℝ)) atTop (𝓝 3) := by
      have hev : ∀ᶠ N : ℕ in atTop, (3 * (N : ℝ) + 1) / (N : ℝ) = 3 + 1 / (N : ℝ) := by
        filter_upwards [eventually_gt_atTop 0] with N hN
        have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp
      rw [tendsto_congr' hev]
      have hinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := by
        simp only [one_div]
        exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      simpa using tendsto_const_nhds.add hinv
    exact (Real.continuousAt_log (by norm_num)).tendsto.comp hratio
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hr1 hr2
  · exact Filter.Eventually.of_forall hlow
  · filter_upwards [eventually_ge_atTop 1] with N hN using hup N hN

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry3InfiniteEvaluation

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry3InfiniteEvaluation

/--
[E_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2.lean)
-/
@[path]
private lemma E_tendsto :
  Tendsto (fun N : ℕ => ∑ k ∈ Finset.Ico (N + 1) (3 * N + 2), (((k : ℝ))⁻¹ - arctan ((k : ℝ))⁻¹))
    atTop (𝓝 0) := by
  have hub : Tendsto (fun N : ℕ => 2 * (((N : ℝ) + 1)⁻¹) ^ 2) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have : Tendsto (fun N : ℕ => 2 * (((N : ℝ) + 1)⁻¹) ^ 2) atTop (𝓝 (2 * (0 : ℝ) ^ 2)) :=
      tendsto_const_nhds.mul (h0.pow 2)
    simpa using this
  apply squeeze_zero (fun N => ?_) (fun N => ?_) hub
  · exact Finset.sum_nonneg (fun k _ => by
    have : arctan ((k : ℝ))⁻¹ ≤ ((k : ℝ))⁻¹ := arctan_le_self (by positivity)
    linarith)
  · have hcard : (Finset.Ico (N + 1) (3 * N + 2)).card = 2 * N + 1 := by rw [Nat.card_Ico]; omega
    have hupos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    calc ∑ k ∈ Finset.Ico (N + 1) (3 * N + 2), (((k : ℝ))⁻¹ - arctan ((k : ℝ))⁻¹)
      ≤ ∑ _k ∈ Finset.Ico (N + 1) (3 * N + 2), (((N : ℝ) + 1)⁻¹) ^ 3 := by
        apply Finset.sum_le_sum
        intro k hk
        have hk1 : N + 1 ≤ k := (Finset.mem_Ico.mp hk).1
        have hkR : ((N : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast hk1
        have h1 : ((k : ℝ))⁻¹ ≤ ((N : ℝ) + 1)⁻¹ := by gcongr
        have h2 : ((k : ℝ))⁻¹ - arctan ((k : ℝ))⁻¹ ≤ ((k : ℝ))⁻¹ ^ 3 := arctan_err _
          (by positivity)
        have h3 : ((k : ℝ))⁻¹ ^ 3 ≤ (((N : ℝ) + 1)⁻¹) ^ 3 := by gcongr
        linarith
      _ = (2 * (N : ℝ) + 1) * (((N : ℝ) + 1)⁻¹) ^ 3 := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring
      _ ≤ 2 * (((N : ℝ) + 1)⁻¹) ^ 2 := by
        have hui : ((N : ℝ) + 1) * ((N : ℝ) + 1)⁻¹ = 1 := by field_simp
        have hu0 : (0 : ℝ) ≤ ((N : ℝ) + 1)⁻¹ := by positivity
        nlinarith [hui, hu0, sq_nonneg (((N : ℝ) + 1)⁻¹), mul_nonneg hu0
          (sq_nonneg (((N : ℝ) + 1)⁻¹))]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry3InfiniteEvaluation

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry3InfiniteEvaluation

/--
[A_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2.lean)
-/
@[path]
private lemma A_tendsto :
  Tendsto (fun N : ℕ => ∑ k ∈ Finset.Ico (N + 1) (3 * N + 2), g k) atTop (𝓝 (Real.log 3)) := by
  have hAeq : (fun N : ℕ => ∑ k ∈ Finset.Ico (N + 1) (3 * N + 2), g k)
    = (fun N : ℕ => (∑ k ∈ Finset.Ico (N + 1) (3 * N + 2), ((k : ℝ))⁻¹)
      - (∑ k ∈ Finset.Ico (N + 1) (3 * N + 2), (((k : ℝ))⁻¹ - arctan ((k : ℝ))⁻¹))) := by
    funext N
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [g, one_div]
    ring
  rw [hAeq]
  simpa using W_tendsto.sub E_tendsto

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry3InfiniteEvaluation

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry3InfiniteEvaluation

/--
[ramanujan_part1_ch2_entry3_infinite_evaluation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry3_infinite_evaluation
  :
-- imply
  HasSum (fun n : ℕ =>
    Real.arctan (10 * ((n : ℝ) + 1) /
    ((3 * ((n : ℝ) + 1) ^ 2 + 2) * (9 * ((n : ℝ) + 1) ^ 2 - 1))))
    (Real.log 3 - Real.pi / 4) := by
-- proof
  change HasSum f (Real.log 3 - Real.pi / 4)
  have hf_nonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    apply arctan_nonneg.mpr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    apply div_nonneg (by positivity)
    apply mul_nonneg (by positivity)
    nlinarith [hn, mul_nonneg hn hn]
  refine (hasSum_iff_tendsto_nat_of_nonneg hf_nonneg (Real.log 3 - Real.pi / 4)).mpr ?_
  have hps : (fun n : ℕ => ∑ i ∈ Finset.range n, f i)
    = (fun n : ℕ => (∑ k ∈ Finset.Ico (n + 1) (3 * n + 2), g k) - Real.pi / 4) := by
    funext n; exact partial_sum n
  rw [hps]
  simpa using A_tendsto.sub_const (Real.pi / 4)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry3InfiniteEvaluation


-- created on 2026-10-20
-- updated on 2026-10-26
