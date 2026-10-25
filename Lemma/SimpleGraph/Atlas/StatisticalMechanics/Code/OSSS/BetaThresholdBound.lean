import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.BetaThresholdBound
open Real Filter Topology Set Finset StatMech StatMech.OSSS StatMech.OSSS.BetaThresholdBound


/--
[btb_limsup_lt_one_of_lt_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaThresholdBound.lean)
-/
@[path]
private lemma btb_limsup_lt_one_of_lt_threshold_eq
  {Sgf : ℝ → ℕ → ℝ}
  {β : ℝ}
-- given
  (hbdd : BddBelow (thresholdSet Sgf))
  (hlt : β < beta1 Sgf) :
-- imply
  Filter.limsup (logRatio (Sgf β)) atTop < 1 := by
-- proof
  apply StatMech.OSSS.BetaThresholdBound.btb_limsup_lt_one_of_lt_threshold Sgf β hbdd hlt

/--
[btb_eventually_ratio_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaThresholdBound.lean)
-/
@[path]
private lemma btb_eventually_ratio_lt_eq
  {u : ℕ → ℝ}
-- given
  (hbdd : IsBoundedUnder (· ≤ ·) atTop u)
  (h : Filter.limsup u atTop < 1) :
-- imply
  ∃ α : ℝ, 0 < α ∧ ∀ᶠ n in atTop, u n < 1 - α := by
-- proof
  apply StatMech.OSSS.BetaThresholdBound.btb_eventually_ratio_lt u hbdd h

/--
[btb_poly_bound_of_ratio_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaThresholdBound.lean)
-/
@[path]
private lemma btb_poly_bound_of_ratio_lt_eq
  {n : ℕ}
  {S α : ℝ}
-- given
  (hn : 2 ≤ n)
  (hS : 0 < S)
  (h : Real.log S / Real.log (n : ℝ) < 1 - α) :
-- imply
  S < (n : ℝ) ^ (1 - α) := by
-- proof
  apply StatMech.OSSS.BetaThresholdBound.btb_poly_bound_of_ratio_lt n S α hn hS h

/--
[btb_poly_bound_of_limsup_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaThresholdBound.lean)
-/
@[path]
private lemma btb_poly_bound_of_limsup_lt_eq
  {Sg : ℕ → ℝ}
-- given
  (hSpos : ∀ n, 2 ≤ n → 0 < Sg n)
  (hbdd : IsBoundedUnder (· ≤ ·) atTop (logRatio Sg))
  (h : Filter.limsup (logRatio Sg) atTop < 1) :
-- imply
  ∃ (N : ℕ) (α : ℝ), 0 < α ∧ ∀ n, N ≤ n → Sg n ≤ (n : ℝ) ^ (1 - α) := by
-- proof
  apply StatMech.OSSS.BetaThresholdBound.btb_poly_bound_of_limsup_lt Sg hSpos hbdd h

/--
[btb_poly_bound_of_lt_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaThresholdBound.lean)
-/
@[path]
private lemma btb_poly_bound_of_lt_threshold_eq
  {Sgf : ℝ → ℕ → ℝ}
  {β : ℝ}
-- given
  (hbddSet : BddBelow (thresholdSet Sgf))
  (hSpos : ∀ n, 2 ≤ n → 0 < Sgf β n)
  (hbdd : IsBoundedUnder (· ≤ ·) atTop (logRatio (Sgf β)))
  (hlt : β < beta1 Sgf) :
-- imply
  ∃ (N : ℕ) (α : ℝ), 0 < α ∧ ∀ n, N ≤ n → Sgf β n ≤ (n : ℝ) ^ (1 - α) := by
-- proof
  apply StatMech.OSSS.BetaThresholdBound.btb_poly_bound_of_lt_threshold Sgf β hbddSet hSpos hbdd hlt

/--
[btb_bddAbove_ratio_of_linear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaThresholdBound.lean)
-/
@[path]
private lemma btb_bddAbove_ratio_of_linear_eq
  {Sg : ℕ → ℝ}
  {C : ℝ}
-- given
  (hC : 1 ≤ C)
  (hSpos : ∀ n, 2 ≤ n → 0 < Sg n)
  (hbound : ∀ n, Sg n ≤ C * (n : ℝ)) :
-- imply
  IsBoundedUnder (· ≤ ·) atTop (logRatio Sg) := by
-- proof
  apply StatMech.OSSS.BetaThresholdBound.btb_bddAbove_ratio_of_linear Sg C hC hSpos hbound

/--
[btb_Sig_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaThresholdBound.lean)
-/
@[path]
private lemma btb_Sig_le_card_eq
  {f : ℕ → ℝ → ℝ}
  {β : ℝ}
  {n : ℕ}
-- given
  (hf : ∀ k, f k β ≤ 1) :
-- imply
  Sig f n β ≤ (n : ℝ) := by
-- proof
  apply StatMech.OSSS.BetaThresholdBound.btb_Sig_le_card f β hf n

/--
[btb_bddAbove_ratio_of_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaThresholdBound.lean)
-/
@[path]
private lemma btb_bddAbove_ratio_of_le_one_eq
  {f : ℕ → ℝ → ℝ}
  {β : ℝ}
-- given
  (hSpos : ∀ n, 2 ≤ n → 0 < Sig f n β)
  (hf : ∀ k, f k β ≤ 1) :
-- imply
  IsBoundedUnder (· ≤ ·) atTop (logRatio (fun n => Sig f n β)) := by
-- proof
  apply StatMech.OSSS.BetaThresholdBound.btb_bddAbove_ratio_of_le_one f β hSpos hf

/--
[btb_subcritical_decay_of_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaThresholdBound.lean)
-/
@[path]
private lemma btb_subcritical_decay_of_threshold_eq
  {f f' : ℕ → ℝ → ℝ}
  {δ β M : ℝ}
-- given
  (hδ : 0 < δ)
  (hMnn : 0 ≤ M)
  (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (f n) (f' n x) x)
  (hfnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ f n x)
  (hfM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, f n x ≤ M)
  (hfmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β → y ≤ x → f k y ≤ f k x)
  (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig f n x)
  (hdiff : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, ((n : ℝ) / Sig f n x) * f n x ≤ f' n x)
  (hSgβpos : ∀ n : ℕ, 2 ≤ n → 0 < Sig f n β)
  (hbddSet : BddBelow (thresholdSet (fun b n => Sig f n b)))
  (hbdd : IsBoundedUnder (· ≤ ·) atTop (logRatio (fun n => Sig f n β)))
  (hlt : β < beta1 (fun b n => Sig f n b)) :
-- imply
  ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n → f n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
-- proof
  apply StatMech.OSSS.BetaThresholdBound.btb_subcritical_decay_of_threshold f f' δ β M hδ hMnn hd hfnn hfM hfmono hSpos hdiff hSgβpos hbddSet hbdd hlt

/--
[btb_fk_q2_subcritical_decay_of_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaThresholdBound.lean)
-/
@[path]
private lemma btb_fk_q2_subcritical_decay_of_threshold_eq
  {θ θ' : ℕ → ℝ → ℝ}
  {δ β M : ℝ}
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
  (hbddSet : BddBelow (thresholdSet (fun b n => Sig θ n b)))
  (hbdd : IsBoundedUnder (· ≤ ·) atTop (logRatio (fun n => Sig θ n β)))
  (hlt : β < beta1 (fun b n => Sig θ n b)) :
-- imply
  ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n → θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
-- proof
  apply StatMech.OSSS.BetaThresholdBound.btb_fk_q2_subcritical_decay_of_threshold θ θ' δ β M hδ hMnn hd hθnn hθM hθmono hSpos hdiff hSgβpos hbddSet hbdd hlt

/--
[btb_fk_q2_subcritical_decay_of_threshold'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaThresholdBound.lean)
-/
@[path]
private lemma btb_fk_q2_subcritical_decay_of_threshold'_eq
  {θ θ' : ℕ → ℝ → ℝ}
  {δ β M : ℝ}
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
  (hlt : β < beta1 (fun b n => Sig θ n b)) :
-- imply
  ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n → θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
-- proof
  apply StatMech.OSSS.BetaThresholdBound.btb_fk_q2_subcritical_decay_of_threshold' θ θ' δ β M hδ hMnn hd hθnn hθM hθmono hSpos hdiff hSgβpos hθ1 hbddSet hlt


-- created on 2026-10-23
