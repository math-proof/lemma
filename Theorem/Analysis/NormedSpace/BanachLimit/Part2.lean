import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Def.Analysis.NormedSpace.BanachLimit.Part2
/-!
# Banach limits on bounded real sequences

A Banach limit is a positive shift-invariant continuous real-linear functional
on `ℕ →ᵇ ℝ` extending ordinary limits. Following Banach, the ordinary limit
functional on convergent sequences is dominated by the sublinear functional
`M x = limsup (Cesàro means of x)` and extended by Hahn–Banach
(`exists_extension_of_le_sublinear`); the bound `|L| ≤ ‖·‖` gives continuity,
and shift-invariance holds because the Cesàro means of `Sx - x` telescope to
`(x n - x 0) / n → 0`.

Source: S. Banach, *Théorie des opérations linéaires* (1932); G. G. Lorentz,
"A contribution to the theory of divergent sequences", *Acta Mathematica* 80
(1948), 167–190, DOI `10.1007/BF02393648`.
-/


namespace FunctionalAnalysis.BanachLimit

open scoped BoundedContinuousFunction

noncomputable section

lemma bddAbove_of_le {u : ℕ → ℝ} {C : ℝ} (h : ∀ n, u n ≤ C) :
    Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) Filter.atTop u :=
  Filter.isBoundedUnder_of ⟨C, h⟩

lemma bddBelow_of_le {u : ℕ → ℝ} {C : ℝ} (h : ∀ n, C ≤ u n) :
    Filter.IsBoundedUnder (fun x1 x2 => x2 ≤ x1) Filter.atTop u :=
  Filter.isBoundedUnder_of ⟨C, h⟩

lemma cobdd_of_bddBelow {u : ℕ → ℝ} {C : ℝ} (h : ∀ n, C ≤ u n) :
    Filter.IsCoboundedUnder (fun x1 x2 => x1 ≤ x2) Filter.atTop u :=
  (bddBelow_of_le h).isCobounded_flip

lemma coe_le_norm (f : BoundedSeq) (n : ℕ) : f n ≤ ‖f‖ := by
  calc f n ≤ |f n| := le_abs_self _
    _ = ‖f n‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖f‖ := BoundedContinuousFunction.norm_coe_le_norm f n

/-- Scalar multiples pass through Cesàro means. -/
lemma cesMean_smul (c : ℝ) (x : BoundedSeq) (n : ℕ) :
    cesMean (c • x) n = c * cesMean x n := by
  unfold cesMean
  simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- Sums pass through Cesàro means. -/
lemma cesMean_add (x y : BoundedSeq) (n : ℕ) :
    cesMean (x + y) n = cesMean x n + cesMean y n := by
  unfold cesMean
  simp only [BoundedContinuousFunction.add_apply, Finset.sum_add_distrib]
  ring

/-- Negation passes through Cesàro means. -/
lemma cesMean_neg (x : BoundedSeq) (n : ℕ) : cesMean (-x) n = -cesMean x n := by
  unfold cesMean
  simp only [BoundedContinuousFunction.neg_apply, Finset.sum_neg_distrib, mul_neg]

/-- Cesàro means are bounded above by the norm. -/
lemma cesMean_le_norm (x : BoundedSeq) (n : ℕ) : cesMean x n ≤ ‖x‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · unfold cesMean
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero]
    exact norm_nonneg _
  · have hsum : ∑ i ∈ Finset.range n, x i ≤ n * ‖x‖ := by
      calc ∑ i ∈ Finset.range n, x i
          ≤ ∑ _i ∈ Finset.range n, ‖x‖ :=
            Finset.sum_le_sum fun i _ => coe_le_norm x i
        _ = n * ‖x‖ := by
            simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc cesMean x n = (n⁻¹ : ℝ) * ∑ i ∈ Finset.range n, x i := rfl
      _ ≤ (n⁻¹ : ℝ) * ((n : ℝ) * ‖x‖) :=
          mul_le_mul_of_nonneg_left hsum
            (inv_nonneg.mpr (Nat.cast_nonneg n))
      _ = ‖x‖ := inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr hn) _

/-- Cesàro means are bounded below by the negated norm. -/
lemma norm_le_cesMean (x : BoundedSeq) (n : ℕ) : -‖x‖ ≤ cesMean x n := by
  linarith [cesMean_le_norm (-x) n, cesMean_neg x n, norm_neg x]

lemma cesMeanBddAbove (x : BoundedSeq) :
    Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) Filter.atTop (cesMean x) :=
  bddAbove_of_le (fun n => cesMean_le_norm x n)

lemma cesMeanBddBelow (x : BoundedSeq) :
    Filter.IsBoundedUnder (fun x1 x2 => x2 ≤ x1) Filter.atTop (cesMean x) :=
  bddBelow_of_le (fun n => norm_le_cesMean x n)

lemma cesMeanCobdd (x : BoundedSeq) :
    Filter.IsCoboundedUnder (fun x1 x2 => x1 ≤ x2) Filter.atTop (cesMean x) :=
  cobdd_of_bddBelow (fun n => norm_le_cesMean x n)

/-- Positive homogeneity of `limsupCes`. -/
lemma limsupCes_hom :
    ∀ c : ℝ, 0 < c → ∀ x : BoundedSeq, limsupCes (c • x) = c * limsupCes x := by
  have hle : ∀ c : ℝ, ∀ x : BoundedSeq, 0 < c →
      Filter.limsup (cesMean (c • x)) Filter.atTop
        ≤ c * Filter.limsup (cesMean x) Filter.atTop := by
    intro c x hc
    show Filter.limsup (cesMean (c • x)) Filter.atTop ≤ _
    rw [Filter.limsup_le_iff (cesMeanCobdd (c • x)) (cesMeanBddAbove (c • x))]
    intro y hy
    have hy' : Filter.limsup (cesMean x) Filter.atTop < y / c := by
      rw [lt_div_iff₀ hc, mul_comm]
      exact hy
    have hev := Filter.eventually_lt_of_limsup_lt hy' (cesMeanBddAbove x)
    filter_upwards [hev] with n hn
    rw [cesMean_smul]
    calc c * cesMean x n < c * (y / c) := mul_lt_mul_of_pos_left hn hc
      _ = y := mul_div_cancel₀ _ (ne_of_gt hc)
  intro c hc x
  have h1 := hle c x hc
  have h2 := hle c⁻¹ (c • x) (inv_pos.mpr hc)
  have e2 : cesMean (c⁻¹ • (c • x)) = cesMean x := by
    funext n
    rw [cesMean_smul, cesMean_smul]
    exact inv_mul_cancel_left₀ (ne_of_gt hc) _
  rw [e2] at h2
  have h3 : c * Filter.limsup (cesMean x) Filter.atTop
      ≤ Filter.limsup (cesMean (c • x)) Filter.atTop := by
    have h4 := mul_le_mul_of_nonneg_left h2 hc.le
    rwa [mul_inv_cancel_left₀ (ne_of_gt hc)] at h4
  change Filter.limsup (cesMean (c • x)) Filter.atTop
    = c * Filter.limsup (cesMean x) Filter.atTop
  exact le_antisymm h1 h3

/-- Subadditivity of `limsupCes`. -/
lemma limsupCes_add :
    ∀ x y : BoundedSeq, limsupCes (x + y) ≤ limsupCes x + limsupCes y := by
  intro x y
  change Filter.limsup (cesMean (x + y)) Filter.atTop
    ≤ Filter.limsup (cesMean x) Filter.atTop
      + Filter.limsup (cesMean y) Filter.atTop
  have e : cesMean (x + y) = (cesMean x + cesMean y) := funext fun n => cesMean_add x y n
  rw [e]
  exact limsup_add_le (cesMeanBddBelow x) (cesMeanBddAbove x) (cesMeanCobdd y)
    (cesMeanBddAbove y)

/-- `limsupCes` is bounded by the norm. -/
lemma limsupCes_bound (x : BoundedSeq) : limsupCes x ≤ ‖x‖ := by
  change Filter.limsup (cesMean x) Filter.atTop ≤ _
  exact Filter.limsup_le_of_le (cesMeanCobdd x)
    (Filter.Eventually.of_forall fun n => cesMean_le_norm x n)

end
end FunctionalAnalysis.BanachLimit
