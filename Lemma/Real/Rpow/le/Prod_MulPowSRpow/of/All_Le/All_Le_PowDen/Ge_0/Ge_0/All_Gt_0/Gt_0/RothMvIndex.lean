import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Real.RpowDivMul.le.PowRpow.of.Le_Pow.Ge_0.Gt_0.Gt_0.Gt_0
import Lemma.Fin.RothRidoutComplement.eq.Sub.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Real Fin


private lemma roth_ridout_weighted_sum_eq
  {m : ℕ}
  (r : Fin m → ℕ)
  (k : RothMvIndex m)
  (μ ν : ℝ)
-- given
  (hk : ∀ h, k h ≤ r h) :
-- imply
  μ * rothMvWeight r k + ν * rothMvWeight r (rothRidoutComplement r k) =
    ∑ h, (μ * (k h : ℝ) / r h + ν * ((r h - k h : ℕ) : ℝ) / r h) := by
-- proof
  unfold rothMvWeight
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  rw [RothRidoutComplement.eq.Sub.of.RothMvIndex, Nat.cast_sub (hk h)]
  ring

/--
[roth_ridout_rpow_weight_le_den_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (Q μ ν : ℝ)
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
  (k : RothMvIndex m)
-- given
  (hQ : 0 < Q)
  (hr : ∀ h, 0 < r h)
  (hμ : 0 ≤ μ)
  (hν : 0 ≤ ν)
  (hpower : ∀ h, Q ≤ ((q h).den : ℝ) ^ r h)
  (hk : ∀ h, k h ≤ r h) :
-- imply
  Real.rpow Q (μ * rothMvWeight r k +
    ν * rothMvWeight r (rothRidoutComplement r k)) ≤
      ∏ h, (Real.rpow ((q h).den : ℝ) μ) ^ k h *
        (Real.rpow ((q h).den : ℝ) ν) ^ (r h - k h) := by
-- proof
  rw [roth_ridout_weighted_sum_eq r k μ ν hk]
  let f : Fin m → ℝ := fun h ↦
    μ * (k h : ℝ) / r h + ν * ((r h - k h : ℕ) : ℝ) / r h
  have hsum : Real.rpow Q (∑ h, f h) = ∏ h, Real.rpow Q (f h) := by
    simpa [f] using Real.rpow_sum_of_pos hQ f Finset.univ
  rw [hsum]
  apply Finset.prod_le_prod₀
  ·
    intro h _
    exact Real.rpow_nonneg hQ.le _
  ·
    intro h _
    have hleft := RpowDivMul.le.PowRpow.of.Le_Pow.Ge_0.Gt_0.Gt_0.Gt_0
      Q (q h).den μ (r h) (k h) hQ (by positivity) (hr h) hμ (hpower h)
    have hright := RpowDivMul.le.PowRpow.of.Le_Pow.Ge_0.Gt_0.Gt_0.Gt_0
      Q (q h).den ν (r h) (r h - k h) hQ (by positivity) (hr h) hν (hpower h)
    calc
      _ = Real.rpow Q (μ * (k h : ℝ) / r h) *
          Real.rpow Q (ν * ((r h - k h : ℕ) : ℝ) / r h) :=
        Real.rpow_add hQ _ _
      _ ≤ (Real.rpow ((q h).den : ℝ) μ) ^ k h *
          (Real.rpow ((q h).den : ℝ) ν) ^ (r h - k h) :=
        mul_le_mul hleft hright (Real.rpow_nonneg hQ.le _)
          (pow_nonneg (Real.rpow_nonneg (by positivity) _) _)


-- created on 2026-10-21
