import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.MaxElementDecomp
open Finset Real StatMech StatMech.Probability


/--
[mxd_maxE_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_maxE_mem_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  [Nonempty ι]
  {S : Finset ι}
-- given
  (hS : S.Nonempty) :
-- imply
  mxd_maxE S ∈ S := by
-- proof
  apply StatMech.Probability.mxd_maxE_mem hS

/--
[mxd_le_maxE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_le_maxE_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  [Nonempty ι]
  {S : Finset ι}
  {x : ι}
-- given
  (hx : x ∈ S) :
-- imply
  x ≤ mxd_maxE S := by
-- proof
  apply StatMech.Probability.mxd_le_maxE hx

/--
[mxd_mem_of_mem_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_mem_of_mem_fiber_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  [Nonempty ι]
  {e : ι}
  {S : Finset ι}
-- given
  (hS : S ∈ mxd_fiber e) :
-- imply
  e ∈ S := by
-- proof
  apply StatMech.Probability.mxd_mem_of_mem_fiber hS

/--
[mxd_fiber_subset_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_fiber_subset_mem_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  [Nonempty ι]
  {e : ι} :
-- imply
  mxd_fiber e ⊆ univ.filter (fun S : Finset ι => e ∈ S) := by
-- proof
  apply StatMech.Probability.mxd_fiber_subset_mem e

/--
[mxd_fiberWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_fiberWeight_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι} :
-- imply
  0 ≤ mxd_fiberWeight p φ e := by
-- proof
  apply StatMech.Probability.mxd_fiberWeight_nonneg p φ e

/--
[mxd_var_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_var_decomp_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = ∑ e : ι, mxd_fiberWeight p φ e := by
-- proof
  apply StatMech.Probability.mxd_var_decomp hp0 hp1 φ

/--
[mxd_dampFiber_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_dampFiber_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  [Nonempty ι]
  {p ρ : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι} :
-- imply
  0 ≤ mxd_dampFiber p ρ φ e := by
-- proof
  apply StatMech.Probability.mxd_dampFiber_nonneg p ρ φ e

/--
[mxd_dampFiber_eq_fiber_perCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_dampFiber_eq_fiber_perCoord_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  [Nonempty ι]
  {p : ℝ}
  {ρ : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  mxd_dampFiber p ρ φ e = ρ ^ 2 * (ptn_sigma p) ^ 2 * ∑ S ∈ mxd_fiber e, (ρ ^ (S.erase e).card) ^ 2 * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S / ptn_sigma p) ^ 2 := by
-- proof
  apply StatMech.Probability.mxd_dampFiber_eq_fiber_perCoord hp0 hp1 ρ φ e

/--
[mxd_dampFiber_le_perCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_dampFiber_le_perCoord_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  [Nonempty ι]
  {p ρ q : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) :
-- imply
  mxd_dampFiber p ρ φ e ≤ ρ ^ 2 * (ptn_sigma p) ^ 2 * (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.mxd_dampFiber_le_perCoord hp0 hp1 h0 h1 hq1 hq2 hρsq φ e

/--
[mxd_dampFiber_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_dampFiber_sum_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  [Nonempty ι]
  {p ρ : ℝ}
  {φ : ConfigSpace ι → Bool} :
-- imply
  (∑ e : ι, mxd_dampFiber p ρ φ e) = ∑ S ∈ (univ.erase (∅ : Finset ι)), (ρ ^ S.card) ^ 2 * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
-- proof
  apply StatMech.Probability.mxd_dampFiber_sum_eq p ρ φ

/--
[mxd_dampFiber_sum_cap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_dampFiber_sum_cap_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  [Nonempty ι]
  {p ρ q : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) :
-- imply
  (∑ e : ι, mxd_dampFiber p ρ φ e) ≤ ρ ^ 2 * (ptn_sigma p) ^ 2 * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.Probability.mxd_dampFiber_sum_cap hp0 hp1 h0 h1 hq1 hq2 hρsq φ

/--
[mxd_dampFiber_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_dampFiber_pos_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  [Nonempty ι]
  {p ρ : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι}
-- given
  (hρ : 0 < ρ)
  (hae : 0 < mxd_fiberWeight p φ e) :
-- imply
  0 < mxd_dampFiber p ρ φ e := by
-- proof
  apply StatMech.Probability.mxd_dampFiber_pos hρ φ e hae

/--
[mxd_logSum_var](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_logSum_var_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  [Nonempty ι]
  {p ρ : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hρ : 0 < ρ)
  (hpos : 0 < ∑ e ∈ univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e), mxd_fiberWeight p φ e) :
-- imply
  (∑ e ∈ univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e), mxd_fiberWeight p φ e) * Real.log ((∑ e ∈ univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e), mxd_fiberWeight p φ e) / (∑ e ∈ univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e), mxd_dampFiber p ρ φ e)) ≤ ∑ e ∈ univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e), mxd_fiberWeight p φ e * Real.log (mxd_fiberWeight p φ e / mxd_dampFiber p ρ φ e) := by
-- proof
  apply StatMech.Probability.mxd_logSum_var hρ φ hpos

/--
[mxd_supp_var](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_supp_var_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ e ∈ univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e), mxd_fiberWeight p φ e) = OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.mxd_supp_var hp0 hp1 φ

/--
[mxd_logSum_gain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_logSum_gain_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  [Nonempty ι]
  {p ρ q : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hρ : 0 < ρ)
  (h0 : ρ ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
  (hVpos : 0 < OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
  (hδ0 : 0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
  (hTpos : 0 < totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :
-- imply
  OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) / (ρ ^ 2 * (ptn_sigma p) ^ 2 * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))) ≤ ∑ e ∈ univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e), mxd_fiberWeight p φ e * Real.log (mxd_fiberWeight p φ e / mxd_dampFiber p ρ φ e) := by
-- proof
  apply StatMech.Probability.mxd_logSum_gain hp0 hp1 hρ h0 hq1 hq2 hρsq φ hVpos hδ0 hTpos

/--
[mxd_rhoOptimise_of_martingaleHC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_rhoOptimise_of_martingaleHC_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  {q : ℝ}
  {H : mxd_martingaleHC_statement q} :
-- imply
  ptn_RhoOptimise q := by
-- proof
  apply StatMech.Probability.mxd_rhoOptimise_of_martingaleHC H

/--
[mxd_decomp_and_gain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_decomp_and_gain_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  [Nonempty ι]
  {p ρ q : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hρ : 0 < ρ)
  (h0 : ρ ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
  (hVpos : 0 < OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
  (hδ0 : 0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
  (hTpos : 0 < totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :
-- imply
  OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = ∑ e : ι, mxd_fiberWeight p φ e ∧ OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) / (ρ ^ 2 * (ptn_sigma p) ^ 2 * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))) ≤ ∑ e ∈ univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e), mxd_fiberWeight p φ e * Real.log (mxd_fiberWeight p φ e / mxd_dampFiber p ρ φ e) := by
-- proof
  apply StatMech.Probability.mxd_decomp_and_gain hp0 hp1 hρ h0 hq1 hq2 hρsq φ hVpos hδ0 hTpos

/--
[mxd_martingaleHC_c0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean)
-/
@[path]
private lemma mxd_martingaleHC_c0_eq
  [Fintype ι]
  [DecidableEq ι]
  [LinearOrder ι]
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  (∑ S : Finset E, (0 : ℝ) * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.mxd_martingaleHC_c0 hp0 hp1 φ u


-- created on 2026-10-23
