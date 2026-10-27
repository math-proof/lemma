import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
open Real Filter Topology Set Finset StatMech StatMech.OSSS StatMech.OSSS.BetaCMatch


/--
[bcm_expBound_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaCMatch.lean)
-/
@[path]
private lemma bcm_expBound_tendsto_zero_eq
  {M Q δ : ℝ}
-- given
  (hQ : 0 < Q)
  (hδ : 0 < δ) :
-- imply
  Tendsto (fun n : ℕ => M * Real.exp (-(((n : ℝ) / Q) * δ))) atTop (𝓝 0) := by
-- proof
  apply StatMech.OSSS.BetaCMatch.bcm_expBound_tendsto_zero M Q δ hQ hδ

/--
[bcm_theta_zero_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaCMatch.lean)
-/
@[path]
private lemma bcm_theta_zero_of_decay_eq
  {θ M Q δ : ℝ}
-- given
  (hQ : 0 < Q)
  (hδ : 0 < δ)
  (hθnn : 0 ≤ θ)
  (hbound : ∀ n : ℕ, θ ≤ M * Real.exp (-(((n : ℝ) / Q) * δ))) :
-- imply
  θ = 0 := by
-- proof
  apply StatMech.OSSS.BetaCMatch.bcm_theta_zero_of_decay θ M Q δ hQ hδ hθnn hbound

/--
[bcm_theta_pos_of_meanField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaCMatch.lean)
-/
@[path]
private lemma bcm_theta_pos_of_meanField_eq
  {θ f β₁ β : ℝ}
-- given
  (hθf : θ = f)
  (hmf : β - β₁ ≤ f)
  (hlt : β₁ < β) :
-- imply
  0 < θ := by
-- proof
  apply StatMech.OSSS.BetaCMatch.bcm_theta_pos_of_meanField θ f β₁ β hθf hmf hlt

/--
[bcm_subcriticalSet_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaCMatch.lean)
-/
@[path]
private lemma bcm_subcriticalSet_le_eq
  {θ : ℝ → ℝ}
  {β₁ : ℝ}
-- given
  (hP2 : ∀ β, β₁ < β → 0 < θ β) :
-- imply
  ∀ β ∈ bcm_subcriticalSet θ, β ≤ β₁ := by
-- proof
  apply StatMech.OSSS.BetaCMatch.bcm_subcriticalSet_le θ β₁ hP2

/--
[bcm_Iio_subset_subcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaCMatch.lean)
-/
@[path]
private lemma bcm_Iio_subset_subcritical_eq
  {θ : ℝ → ℝ}
  {β₁ : ℝ}
-- given
  (hP1 : ∀ β, β < β₁ → θ β = 0) :
-- imply
  Iio β₁ ⊆ bcm_subcriticalSet θ := by
-- proof
  apply StatMech.OSSS.BetaCMatch.bcm_Iio_subset_subcritical θ β₁ hP1

/--
[bcm_betaC_eq_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaCMatch.lean)
-/
@[path]
private lemma bcm_betaC_eq_threshold_eq
  {θ : ℝ → ℝ}
  {β₁ : ℝ}
-- given
  (hP1 : ∀ β, β < β₁ → θ β = 0)
  (hP2 : ∀ β, β₁ < β → 0 < θ β) :
-- imply
  sSup (bcm_subcriticalSet θ) = β₁ := by
-- proof
  apply StatMech.OSSS.BetaCMatch.bcm_betaC_eq_threshold θ β₁ hP1 hP2

/--
[bcm_betaC_eq_beta1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaCMatch.lean)
-/
@[path]
private lemma bcm_betaC_eq_beta1_eq
  {θ : ℕ → ℝ → ℝ}
  {Θ : ℝ → ℝ}
  {M : ℝ}
  {Qf δf : ℝ → ℝ}
-- given
  (hdecay : ∀ β, β < beta1 (fun b n => Sig θ n b) → 0 ≤ Θ β ∧ 0 < Qf β ∧ 0 < δf β ∧ ∀ n : ℕ, Θ β ≤ M * Real.exp (-(((n : ℝ) / Qf β) * δf β)))
  (hmf : ∀ β, beta1 (fun b n => Sig θ n b) < β → β - beta1 (fun b n => Sig θ n b) ≤ Θ β) :
-- imply
  sSup (bcm_subcriticalSet Θ) = beta1 (fun b n => Sig θ n b) := by
-- proof
  apply StatMech.OSSS.BetaCMatch.bcm_betaC_eq_beta1 θ Θ M Qf δf hdecay hmf

/--
[bcm_fk_q2_subcritical_decay_of_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaCMatch.lean)
-/
@[path]
private lemma bcm_fk_q2_subcritical_decay_of_betaC_eq
  {θ θ' : ℕ → ℝ → ℝ}
  {Θ : ℝ → ℝ}
  {δ β M : ℝ}
  {Qf δf : ℝ → ℝ}
-- given
  (hδ : 0 < δ)
  (hMnn : 0 ≤ M)
  (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (θ n) (θ' n x) x)
  (hθnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ θ n x)
  (hθM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x ≤ M)
  (hθmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β → y ≤ x → θ k y ≤ θ k x)
  (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig θ n x)
  (hdiff : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, ((n : ℝ) / Sig θ n x) * θ n x ≤ θ' n x)
  (hSgβpos : ∀ n : ℕ, 2 ≤ n → 0 < Sig θ n β)
  (hθ1 : ∀ k, θ k β ≤ 1)
  (hbddSet : BddBelow (thresholdSet (fun b n => Sig θ n b)))
  (hdecay : ∀ b, b < beta1 (fun b n => Sig θ n b) → 0 ≤ Θ b ∧ 0 < Qf b ∧ 0 < δf b ∧ ∀ n : ℕ, Θ b ≤ M * Real.exp (-(((n : ℝ) / Qf b) * δf b)))
  (hmf : ∀ b, beta1 (fun b n => Sig θ n b) < b → b - beta1 (fun b n => Sig θ n b) ≤ Θ b)
  (hβc : β < sSup (bcm_subcriticalSet Θ)) :
-- imply
  ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n → θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
-- proof
  apply StatMech.OSSS.BetaCMatch.bcm_fk_q2_subcritical_decay_of_betaC θ θ' Θ δ β M Qf δf hδ hMnn hd hθnn hθM hθmono hSpos hdiff hSgβpos hθ1 hbddSet hdecay hmf hβc


-- created on 2026-10-23
