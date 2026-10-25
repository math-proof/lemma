import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.BourgainPerCoord.Part2
open Finset Real StatMech StatMech.Probability


/--
[bph_noiseOp_sum_walsh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean)
-/
@[path]
private lemma bph_noiseOp_sum_walsh_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {s : Finset (Finset ι)}
  {a : Finset ι → ℝ}
  {T : Finset ι → Finset ι} :
-- imply
  bnt_noiseOp ρ (fun x => ∑ S ∈ s, a S * khc_walshChar (T S) x) = fun x => ∑ S ∈ s, (a S * ρ ^ (T S).card) * khc_walshChar (T S) x := by
-- proof
  apply StatMech.Probability.bph_noiseOp_sum_walsh ρ s a T

/--
[bph_noiseOp_l2sq_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean)
-/
@[path]
private lemma bph_noiseOp_l2sq_relabel_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {s : Finset (Finset ι)}
  {a : Finset ι → ℝ}
  {T : Finset ι → Finset ι}
-- given
  (hTinj : Set.InjOn T s) :
-- imply
  bnt_uexp (fun x => (bnt_noiseOp ρ (fun x => ∑ S ∈ s, a S * khc_walshChar (T S) x) x) ^ 2) = ∑ S ∈ s, (ρ ^ (T S).card) ^ 2 * (a S) ^ 2 := by
-- proof
  apply StatMech.Probability.bph_noiseOp_l2sq_relabel ρ s a T hTinj

/--
[bph_noiseOp_deriv_l2sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean)
-/
@[path]
private lemma bph_noiseOp_deriv_l2sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {f : ConfigSpace ι → ℝ}
  {e : ι} :
-- imply
  bnt_uexp (fun x => (bnt_noiseOp ρ (bph_deriv f e) x) ^ 2) = ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S), (ρ ^ (S.erase e).card) ^ 2 * (4 * (khc_fourierCoeff f S) ^ 2) := by
-- proof
  apply StatMech.Probability.bph_noiseOp_deriv_l2sq ρ f e

/--
[bph_abs_deriv_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean)
-/
@[path]
private lemma bph_abs_deriv_rpow_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι}
  {ω : ConfigSpace ι}
-- given
  (hq : 0 < q) :
-- imply
  |bph_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e ω| ^ q = (bph_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e ω) ^ 2 := by
-- proof
  apply StatMech.Probability.bph_abs_deriv_rpow hq φ e ω

/--
[bph_uexp_deriv_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean)
-/
@[path]
private lemma bph_uexp_deriv_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool}
  {e : ι} :
-- imply
  bnt_uexp (fun ω => (bph_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e ω) ^ 2) = OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e := by
-- proof
  apply StatMech.Probability.bph_uexp_deriv_sq φ e

/--
[bph_qnormPow_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean)
-/
@[path]
private lemma bph_qnormPow_deriv_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι}
-- given
  (hq : 0 < q) :
-- imply
  bnt_qnormPow q (bph_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e) = OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e := by
-- proof
  apply StatMech.Probability.bph_qnormPow_deriv hq φ e

/--
[bph_qnorm_deriv_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean)
-/
@[path]
private lemma bph_qnorm_deriv_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι} :
-- imply
  (bnt_qnorm (1 + ρ ^ 2) (bph_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e)) ^ 2 = (OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (1 + ρ ^ 2)) := by
-- proof
  apply StatMech.Probability.bph_qnorm_deriv_sq φ e

/--
[bph_perCoord_hc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean)
-/
@[path]
private lemma bph_perCoord_hc_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S), (ρ ^ (S.erase e).card) ^ 2 * (4 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)) ≤ (OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (1 + ρ ^ 2)) := by
-- proof
  apply StatMech.Probability.bph_perCoord_hc h0 h1 φ e

/--
[bph_summed_hc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean)
-/
@[path]
private lemma bph_summed_hc_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  (∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2 * (4 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2))) ≤ ∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (1 + ρ ^ 2)) := by
-- proof
  apply StatMech.Probability.bph_summed_hc h0 h1 φ

/--
[bph_cap_term](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean)
-/
@[path]
private lemma bph_cap_term_eq
  [Fintype ι]
  [DecidableEq ι]
  {x δ θ : ℝ}
-- given
  (hx : 0 ≤ x)
  (hcap : x ≤ δ)
  (hθ : 1 ≤ θ) :
-- imply
  x ^ θ ≤ δ ^ (θ - 1) * x := by
-- proof
  apply StatMech.Probability.bph_cap_term x δ θ hx hcap hθ

/--
[bph_cap_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean)
-/
@[path]
private lemma bph_cap_sum_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {ρ : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  (∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (1 + ρ ^ 2))) ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2) - 1) * (∑ S : Finset ι, 4 * (S.card : ℝ) * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
-- proof
  apply StatMech.Probability.bph_cap_sum h0 h1 φ

/--
[bph_capped_hc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean)
-/
@[path]
private lemma bph_capped_hc_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {ρ : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (ρ ^ (S.card - 1)) ^ 2 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2) - 1) * (∑ S : Finset ι, 4 * (S.card : ℝ) * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
-- proof
  apply StatMech.Probability.bph_capped_hc h0 h1 φ

/--
[bph_rhoOptimise_hyp_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean)
-/
@[path]
private lemma bph_rhoOptimise_hyp_holds_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → (∑ S : Finset ι, 4 * (S.card : ℝ) * (ρ ^ (S.card - 1)) ^ 2 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2) - 1) * (∑ S : Finset ι, 4 * (S.card : ℝ) * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
-- proof
  apply StatMech.Probability.bph_rhoOptimise_hyp_holds φ

/--
[bph_rhoOptimise_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean)
-/
@[path]
private lemma bph_rhoOptimise_zero_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  bph_RhoOptimise 0 := by
-- proof
  apply StatMech.Probability.bph_rhoOptimise_zero

/--
[bph_logOptimisation_of_rho](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean)
-/
@[path]
private lemma bph_logOptimisation_of_rho_eq
  [Fintype ι]
  [DecidableEq ι]
  {c : ℝ}
  {H : bph_RhoOptimise c} :
-- imply
  kls_LogOptimisation c := by
-- proof
  apply StatMech.Probability.bph_logOptimisation_of_rho H

/--
[bph_KKL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean)
-/
@[path]
private lemma bph_KKL_eq
  [Fintype ι]
  [DecidableEq ι]
  {c : ℝ}
  {H : bph_RhoOptimise c} :
-- imply
  KKLHypercontractive (1 / 2 : ℝ) c := by
-- proof
  apply StatMech.Probability.bph_KKL H


-- created on 2026-10-23
