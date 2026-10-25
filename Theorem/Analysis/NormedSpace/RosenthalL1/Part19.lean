/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.NormedSpace.RosenthalL1.Part18
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_uniform_lower_bound_of_assignments
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (y : ℕ → E) (epsilon : ℝ) (hepsilon : 0 < epsilon) (u v : 𝕜)
    (hcenters : epsilon ≤ dist u v + 2 * (epsilon / 64))
    (hassign : ∀ P Q : Finset ℕ, Disjoint P Q →
      ∃ g : RosenthalDualBall 𝕜 E,
        (∀ i ∈ P,
          dist (rosenthalDualEval (𝕜 := 𝕜) y i g) u ≤ epsilon / 64) ∧
        ∀ i ∈ Q,
          dist (rosenthalDualEval (𝕜 := 𝕜) y i g) v ≤ epsilon / 64) :
    HasUniformL1LowerBound (𝕜 := 𝕜) y := by
  refine ⟨epsilon / 16, by positivity, ?_⟩
  intro a
  let total : ℝ := ∑ i ∈ a.support, ‖a i‖
  let S : E := ∑ i ∈ a.support, a i • y i
  obtain ⟨P, hP, hquadrant⟩ := rosenthal_exists_large_quadrant a.support
    (fun i => a i * (v - u))
  obtain ⟨g, hgu, hgv⟩ := hassign (a.support \ P) P Finset.sdiff_disjoint
  obtain ⟨h, hhu, _⟩ := hassign a.support ∅ (by simp)
  let F := rosenthalDualBallStrong g
  let G := rosenthalDualBallStrong h
  let Z : 𝕜 := ∑ i ∈ P, a i * (v - u)
  have herror : ‖F S - G S - Z‖ ≤ 2 * (epsilon / 64) * total := by
    simpa [F, G, S, Z, total] using
      rosenthal_dual_sum_error y u v (epsilon / 64) a P hP g h hgu hgv hhu
  have hF : ‖F S‖ ≤ ‖S‖ := by
    calc
      ‖F S‖ ≤ ‖F‖ * ‖S‖ := ContinuousLinearMap.le_opNorm F S
      _ ≤ 1 * ‖S‖ := mul_le_mul_of_nonneg_right
        (rosenthal_dualBallStrong_norm_le g) (norm_nonneg _)
      _ = ‖S‖ := one_mul _
  have hG : ‖G S‖ ≤ ‖S‖ := by
    calc
      ‖G S‖ ≤ ‖G‖ * ‖S‖ := ContinuousLinearMap.le_opNorm G S
      _ ≤ 1 * ‖S‖ := mul_le_mul_of_nonneg_right
        (rosenthal_dualBallStrong_norm_le h) (norm_nonneg _)
      _ = ‖S‖ := one_mul _
  have hdiff : ‖F S - G S‖ ≤ 2 * ‖S‖ :=
    (norm_sub_le _ _).trans (by linarith)
  have htriangle : ‖Z‖ ≤ ‖F S - G S - Z‖ + ‖F S - G S‖ := by
    calc
      ‖Z‖ = ‖(Z - (F S - G S)) + (F S - G S)‖ := by congr 1; ring
      _ ≤ ‖Z - (F S - G S)‖ + ‖F S - G S‖ := norm_add_le _ _
      _ = ‖F S - G S - Z‖ + ‖F S - G S‖ := by rw [norm_sub_rev]
  have hZupper : ‖Z‖ ≤ 2 * (epsilon / 64) * total + 2 * ‖S‖ :=
    htriangle.trans (add_le_add herror hdiff)
  have hnormsum : (∑ i ∈ a.support, ‖a i * (v - u)‖) = dist u v * total := by
    simp only [norm_mul]
    rw [← Finset.sum_mul]
    simp [total, dist_eq_norm, norm_sub_rev, mul_comm]
  have hZlower : dist u v * total / 4 ≤ ‖Z‖ := by
    rw [hnormsum] at hquadrant
    simpa [Z] using hquadrant
  have htotal : 0 ≤ total := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcenter' : epsilon - 2 * (epsilon / 64) ≤ dist u v := by linarith
  have hscaled := mul_le_mul_of_nonneg_right hcenter' htotal
  change epsilon / 16 * total ≤ ‖S‖
  nlinarith

theorem rosenthal_dualEval_bounded
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → E) (hx : Bornology.IsBounded (Set.range x)) :
    ∃ B : ℝ, ∀ n (g : RosenthalDualBall 𝕜 E),
      ‖rosenthalDualEval (𝕜 := 𝕜) x n g‖ ≤ B := by
  obtain ⟨B, hB⟩ := hx.subset_closedBall 0
  refine ⟨B, ?_⟩
  intro n g
  have hxn : ‖x n‖ ≤ B := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hB ⟨n, rfl⟩
  calc
    ‖rosenthalDualEval (𝕜 := 𝕜) x n g‖ =
        ‖rosenthalDualBallStrong g (x n)‖ := by
      rw [rosenthal_dualEval_eq_strong]
    _ ≤ ‖rosenthalDualBallStrong g‖ * ‖x n‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖x n‖ := mul_le_mul_of_nonneg_right
      (rosenthal_dualBallStrong_norm_le g) (norm_nonneg _)
    _ ≤ B := by simpa using hxn

theorem rosenthal_weakCauchy_of_dualBall
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → E) (φ : ℕ → ℕ)
    (h : ∀ g : RosenthalDualBall 𝕜 E, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N, ∀ m n, N ≤ m → N ≤ n →
        dist (rosenthalDualEval (𝕜 := 𝕜) x (φ m) g)
          (rosenthalDualEval (𝕜 := 𝕜) x (φ n) g) < epsilon) :
    ∀ (f : E →L[𝕜] 𝕜) (epsilon : ℝ), 0 < epsilon →
      ∃ N, ∀ m n, N ≤ m → N ≤ n →
        ‖f (x (φ m)) - f (x (φ n))‖ < epsilon := by
  intro f epsilon hepsilon
  by_cases hf : f = 0
  · subst f
    exact ⟨0, fun _ _ _ _ => by simpa using hepsilon⟩
  · have hfnorm : 0 < ‖f‖ := norm_pos_iff.mpr hf
    let c : 𝕜 := ((‖f‖⁻¹ : ℝ) : 𝕜)
    let f' : E →L[𝕜] 𝕜 := c • f
    have hcnorm : ‖c‖ = ‖f‖⁻¹ := by
      simp [c]
    have hf'norm : ‖f'‖ ≤ 1 := by
      change ‖c • f‖ ≤ 1
      rw [norm_smul, hcnorm, inv_mul_cancel₀ (ne_of_gt hfnorm)]
    let g : RosenthalDualBall 𝕜 E :=
      ⟨StrongDual.toWeakDual f', by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hf'norm⟩
    have hepsdiv : 0 < epsilon / ‖f‖ := div_pos hepsilon hfnorm
    obtain ⟨N, hN⟩ := h g (epsilon / ‖f‖) hepsdiv
    refine ⟨N, ?_⟩
    intro m n hm hn
    have hclose := hN m n hm hn
    change dist ((StrongDual.toWeakDual f') (x (φ m)))
      ((StrongDual.toWeakDual f') (x (φ n))) < epsilon / ‖f‖ at hclose
    rw [StrongDual.toWeakDual_apply, StrongDual.toWeakDual_apply] at hclose
    have hscaled : ‖f‖⁻¹ * ‖f (x (φ m)) - f (x (φ n))‖ < epsilon / ‖f‖ := by
      change dist (c * f (x (φ m))) (c * f (x (φ n))) < epsilon / ‖f‖ at hclose
      rw [dist_eq_norm, ← mul_sub, norm_mul, hcnorm] at hclose
      exact hclose
    have hmul := mul_lt_mul_of_pos_left hscaled hfnorm
    calc
      ‖f (x (φ m)) - f (x (φ n))‖ =
          ‖f‖ * (‖f‖⁻¹ * ‖f (x (φ m)) - f (x (φ n))‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hfnorm), one_mul]
      _ < ‖f‖ * (epsilon / ‖f‖) := hmul
      _ = epsilon := by
        rw [div_eq_mul_inv]
        calc
          ‖f‖ * (epsilon * ‖f‖⁻¹) = epsilon * (‖f‖ * ‖f‖⁻¹) := by ring
          _ = epsilon := by rw [mul_inv_cancel₀ (ne_of_gt hfnorm), mul_one]

theorem rosenthal_exists_paired_subsequence_of_not_eventually_close
    {α : Type*} [PseudoMetricSpace α] (u : ℕ → α) {ε : ℝ} (hε : 0 < ε)
    (h : ¬∃ N, ∀ m n, N ≤ m → N ≤ n → dist (u m) (u n) < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ j, ε ≤ dist (u (φ (2 * j))) (u (φ (2 * j + 1))) := by
  push Not at h
  have hpick : ∀ N : ℕ, ∃ a b : ℕ,
      N ≤ a ∧ a < b ∧ ε ≤ dist (u a) (u b) := by
    intro N
    obtain ⟨m, n, hm, hn, hmn⟩ := h N
    have hne : m ≠ n := by
      intro heq
      subst n
      simpa using (lt_of_lt_of_le hε hmn).ne'
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨m, n, hm, hlt, hmn⟩
    · exact ⟨n, m, hn, hgt, by simpa [dist_comm] using hmn⟩
  choose lo hi hlo hlthi hgap using hpick
  let next : ℕ → ℕ := fun N => hi N + 1
  let bound : ℕ → ℕ := fun n => next^[n] 0
  let left : ℕ → ℕ := fun n => lo (bound n)
  let right : ℕ → ℕ := fun n => hi (bound n)
  let φ : ℕ → ℕ := fun n =>
    if n % 2 = 0 then left (n / 2) else right (n / 2)
  have hbound_succ : ∀ n, bound (n + 1) = right n + 1 := by
    intro n
    rw [show n + 1 = n.succ from rfl]
    exact Function.iterate_succ_apply' next n 0
  have hφeven : ∀ n, φ (2 * n) = left n := by
    intro n
    have hdiv : 2 * n / 2 = n := by omega
    have hmod : 2 * n % 2 = 0 := by omega
    simp only [φ, hdiv, hmod, ↓reduceIte]
  have hφodd : ∀ n, φ (2 * n + 1) = right n := by
    intro n
    have hdiv : (2 * n + 1) / 2 = n := by omega
    have hmod : (2 * n + 1) % 2 = 1 := by omega
    simp only [φ, hdiv, hmod, one_ne_zero, ↓reduceIte]
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [hφeven, hφodd]
      exact hlthi _
    · rw [hφodd, show 2 * k + 1 + 1 = 2 * (k + 1) by omega, hφeven]
      have hnext : right k + 1 ≤ left (k + 1) := by
        rw [← hbound_succ]
        exact hlo _
      omega
  exact ⟨φ, hφ, fun j => by rw [hφeven, hφodd]; exact hgap _⟩

theorem rosenthal_eventually_close_of_no_gap_paired
    {K α : Type*} [PseudoMetricSpace α] (f : ℕ → K → α) {ε : ℝ} (hε : 0 < ε)
    {φ : ℕ → ℕ}
    (hno : ∀ θ : ℕ → ℕ, StrictMono θ →
      ¬rosenthalPaired (rosenthalGap f ε) (φ ∘ θ)) :
    ∀ k : K, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      dist (f (φ m) k) (f (φ n) k) < ε := by
  intro k
  by_contra hclose
  obtain ⟨θ, hθ, hgap⟩ :=
    rosenthal_exists_paired_subsequence_of_not_eventually_close
      (fun n => f (φ n) k) hε hclose
  apply hno θ hθ
  exact ⟨k, fun j => by simpa [rosenthalGap, Function.comp_def] using hgap j⟩

end FunctionalAnalysis.RosenthalL1Wanted
