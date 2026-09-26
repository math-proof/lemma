import sympy.stats.iterates
import sympy.stats.lyapunov
import sympy.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.EMetricSpace.Lipschitz
import Lemma.LyapunovCandidate.Any_And_Ge_0_All_LeInner.of.LyapunovCandidate
import Lemma.LyapunovCandidate.Any_Ge_0AndAll_LeAddNorm_MulAddSqrtUFnSub1.of.LyapunovCandidate
open Filter MeasureTheory
set_option maxHeartbeats 1000000


@[main]
private lemma main
  {d : ℕ}
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω}
  {x e₁ e₂ : ℕ → Ω → EuclideanVec d}
  {x₀ z : EuclideanVec d}
  {f : EuclideanVec d → EuclideanVec d}
  {α : ℕ → ℝ}
  {φ : EuclideanVec d → ℝ}
  {φ' : EuclideanVec d → EuclideanVec d}
-- given
  (h₀ : Iterates x x₀ f e₁ e₂ α)
  (h₁ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n, ‖e₁ (n + 1) ω‖ ≤ C * α n * (‖x n ω‖ + 1))
  (h₂ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n, ‖e₂ (n + 1) ω‖ ≤ C * α n ^ 2 * (‖x n ω‖ + 1))
  (h₃ : z = f z)
  (h₄ : ∃ L, LipschitzWith L f)
  (h₅ : ∀ n, 0 < α n)
  (h₆ : Summable fun n => α n ^ 2)
  (h₇ : LyapunovFunction φ φ' f) :
-- imply
  ∃ B₁ B₂, 0 < B₁ ∧ 0 ≤ B₂ ∧ ∃ n₀, ∀ᵐ ω ∂μ, ∀ n ≥ n₀,
    φ (x (n + 1) ω - z) ≤
      (1 - B₁ * α n) * φ (x n ω - z) + inner ℝ (φ' (x n ω - z)) (e₁ (n + 1) ω) + B₂ * α n ^ 2 := by
-- proof
  obtain ⟨Lf, hLf⟩ := h₄
  obtain ⟨L, hL, hsmooth⟩ := h₇.smooth
  obtain ⟨η, hη, hdec⟩ := h₇.decrease
  obtain ⟨C₀, hC₀, hnorm⟩ := h₇.norm_le
  obtain ⟨C₁, hC₁, hle⟩ := h₇.le_norm
  obtain ⟨C₃, hC₃, he₁⟩ := h₁
  obtain ⟨C₄, hC₄, he₂⟩ := h₂
  obtain ⟨C₅, hC₅, hadd⟩ :=
    LyapunovCandidate.Any_Ge_0AndAll_LeAddNorm_MulAddSqrtUFnSub1.of.LyapunovCandidate (a := 1) h₇.toLyapunovCandidate z
  obtain ⟨C₆, hC₆, hinner⟩ := LyapunovCandidate.Any_And_Ge_0_All_LeInner.of.LyapunovCandidate h₇.toLyapunovCandidate
  set K := C₆ * C₁ * C₄ * C₅ with hK_def
  set M₁ := ((Lf : ℝ) + 1) ^ 2 * C₀ ^ 2 with hM₁_def
  set M₂ := 2 * (C₃ * C₅) ^ 2 + 2 * (C₄ * C₅) ^ 2 with hM₂_def
  set A := 2 * K + 3 * L / 2 * (M₁ + M₂) with hA_def
  set B := K + 3 * L / 2 * M₂ with hB_def
  have hK : 0 ≤ K := by positivity
  have hM₁ : 0 ≤ M₁ := by positivity
  have hM₂ : 0 ≤ M₂ := by positivity
  have hA : 0 ≤ A := by positivity
  set ε := min 1 (η / (2 * (A + 1))) with hε_def
  have hε : 0 < ε := lt_min one_pos (by positivity)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
    (h₆.tendsto_atTop_zero.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε ^ 2)))
  refine ⟨η / 2, B, by positivity, by positivity, n₀, ?_⟩
  filter_upwards [he₁, he₂] with ω h₁ h₂ n hn
  have ha := h₅ n
  have haε : α n < ε := lt_of_pow_lt_pow_left₀ 2 hε.le (hn₀ n hn)
  have ha1 : α n ≤ 1 := haε.le.trans (min_le_left _ _)
  have haη : α n * A ≤ η / 2 := by
    have h := haε.le.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  set v := x n ω - z with hv
  set p := φ v with hp_def
  set s := √p with hs_def
  have hp : 0 ≤ p := h₇.nonneg v
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = p := Real.sq_sqrt hp
  have hs1 : s ≤ p + 1 := by nlinarith [sq_nonneg (s - 1)]
  have hsq1 : (s + 1) ^ 2 ≤ 2 * (p + 1) := by nlinarith [sq_nonneg (s - 1)]
  set g := f (x n ω) - x n ω with hg_def
  have hΔ : x (n + 1) ω - z - v = α n • g + e₁ (n + 1) ω + e₂ (n + 1) ω := by
    rw [hv, hg_def, h₀.step]
    abel
  have hxn : ‖x n ω‖ + 1 ≤ C₅ * (s + 1) := hadd (x n ω)
  have hg : ‖g‖ ≤ ((Lf : ℝ) + 1) * C₀ * s := by
    have e : g = (f (x n ω) - f z) - v := by
      rw [hg_def, hv, ← h₃]
      abel
    have h₈ : ‖f (x n ω) - f z‖ ≤ Lf * ‖v‖ := hLf.norm_sub_le _ _
    have h₉ : ‖g‖ ≤ ‖f (x n ω) - f z‖ + ‖v‖ := by
      rw [e]
      exact norm_sub_le _ _
    have h₁₀ : ‖v‖ ≤ C₀ * s := hnorm v
    have h₁₁ : ((Lf : ℝ) + 1) * ‖v‖ ≤ ((Lf : ℝ) + 1) * (C₀ * s) := by gcongr
    have h₁₂ : ‖g‖ ≤ ((Lf : ℝ) + 1) * ‖v‖ := by linarith
    exact h₁₂.trans (h₁₁.trans_eq (by ring))
  have hn₁ : ‖e₁ (n + 1) ω‖ ≤ C₃ * C₅ * α n * (s + 1) := by
    calc _ ≤ C₃ * α n * (‖x n ω‖ + 1) := h₁ n
      _ ≤ C₃ * α n * (C₅ * (s + 1)) := by gcongr
      _ = _ := by ring
  have hn₂ : ‖e₂ (n + 1) ω‖ ≤ C₄ * C₅ * α n ^ 2 * (s + 1) := by
    calc _ ≤ C₄ * α n ^ 2 * (‖x n ω‖ + 1) := h₂ n
      _ ≤ C₄ * α n ^ 2 * (C₅ * (s + 1)) := by gcongr
      _ = _ := by ring
  have hT₂ : inner ℝ (φ' v) (e₂ (n + 1) ω) ≤ K * α n ^ 2 * (2 * p + 1) := by
    calc _ ≤ C₆ * s * √(φ (e₂ (n + 1) ω)) := hinner _ _
      _ ≤ C₆ * s * (C₁ * (C₄ * C₅ * α n ^ 2 * (s + 1))) :=
          mul_le_mul_of_nonneg_left ((hle _).trans (mul_le_mul_of_nonneg_left hn₂ hC₁)) (by positivity)
      _ = K * α n ^ 2 * (s ^ 2 + s) := by rw [hK_def]; ring
      _ ≤ K * α n ^ 2 * (2 * p + 1) :=
          mul_le_mul_of_nonneg_left (by linarith only [hs2, hs1]) (by positivity)
  have hD : ‖α n • g + e₁ (n + 1) ω + e₂ (n + 1) ω‖ ^ 2 ≤ 3 * α n ^ 2 * (M₁ * p + M₂ * (p + 1)) := by
    have htri : ‖α n • g + e₁ (n + 1) ω + e₂ (n + 1) ω‖ ≤ α n * ‖g‖ + ‖e₁ (n + 1) ω‖ + ‖e₂ (n + 1) ω‖ := by
      have h₈ := norm_add_le (α n • g + e₁ (n + 1) ω) (e₂ (n + 1) ω)
      have h₉ := norm_add_le (α n • g) (e₁ (n + 1) ω)
      rw [norm_smul, Real.norm_of_nonneg ha.le] at h₉
      linarith
    have hag : α n * ‖g‖ ≤ α n * (((Lf : ℝ) + 1) * C₀ * s) := by gcongr
    have hn₂' : ‖e₂ (n + 1) ω‖ ≤ C₄ * C₅ * α n * (s + 1) := by
      have h₈ : α n ^ 2 ≤ α n := by rw [sq]; exact mul_le_of_le_one_left ha.le ha1
      have h₉ : 0 ≤ C₄ * C₅ * (s + 1) := by positivity
      have h₁₀ := mul_le_mul_of_nonneg_left h₈ h₉
      linarith only [hn₂, h₁₀]
    obtain ⟨u₁, hu₁⟩ : ∃ u, u = α n * (((Lf : ℝ) + 1) * C₀ * s) := ⟨_, rfl⟩
    obtain ⟨u₂, hu₂⟩ : ∃ u, u = C₃ * C₅ * α n * (s + 1) := ⟨_, rfl⟩
    obtain ⟨u₃, hu₃⟩ : ∃ u, u = C₄ * C₅ * α n * (s + 1) := ⟨_, rfl⟩
    have hle₃ : ‖α n • g + e₁ (n + 1) ω + e₂ (n + 1) ω‖ ≤ u₁ + u₂ + u₃ := by rw [hu₁, hu₂, hu₃]; linarith
    have h3a : 0 ≤ 3 * α n ^ 2 := by positivity
    have hC : ((C₃ * C₅) ^ 2 + (C₄ * C₅) ^ 2) * (s + 1) ^ 2 ≤ M₂ * (p + 1) := by
      have h₈ := mul_le_mul_of_nonneg_left hsq1 (by positivity : (0 : ℝ) ≤ (C₃ * C₅) ^ 2 + (C₄ * C₅) ^ 2)
      rw [hM₂_def]
      linarith
    calc _ ≤ (u₁ + u₂ + u₃) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle₃ 2
      _ ≤ 3 * (u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2) := by
          nlinarith [sq_nonneg (u₁ - u₂), sq_nonneg (u₂ - u₃), sq_nonneg (u₁ - u₃)]
      _ = 3 * α n ^ 2 * (M₁ * s ^ 2 + ((C₃ * C₅) ^ 2 + (C₄ * C₅) ^ 2) * (s + 1) ^ 2) := by
          rw [hu₁, hu₂, hu₃, hM₁_def]
          ring
      _ ≤ 3 * α n ^ 2 * (M₁ * p + M₂ * (p + 1)) := by
          rw [hs2]
          exact mul_le_mul_of_nonneg_left (by linarith) h3a
  have hsm := hsmooth v (x (n + 1) ω - z)
  rw [hΔ, inner_add_right, inner_add_right, inner_smul_right] at hsm
  have hdec' : inner ℝ (φ' v) g ≤ -η * p := hdec z h₃ (x n ω)
  have h₈ := mul_le_mul_of_nonneg_left hdec' ha.le
  have h₉ := mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ L / 2)
  have h₁₀ := mul_le_mul_of_nonneg_right haη (mul_nonneg ha.le hp)
  have h₁₁ : A * (α n ^ 2 * p) = 2 * K * α n ^ 2 * p + 3 * L / 2 * (M₁ + M₂) * α n ^ 2 * p := by
    rw [hA_def]
    ring
  rw [hB_def]
  linarith


-- created on 2026-09-26