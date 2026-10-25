import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.RussoPrefactor
open Real Finset StatMech StatMech.OSSS StatMech.OSSS.RussoPrefactor


/--
[rp_denom_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RussoPrefactor.lean)
-/
@[path]
private lemma rp_denom_pos_eq
  {J β : ℝ}
-- given
  (hJ : 0 < J)
  (hβ : 0 < β) :
-- imply
  0 < Real.exp (β * J) - 1 := by
-- proof
  apply StatMech.OSSS.RussoPrefactor.rp_denom_pos hJ hβ

/--
[rp_prefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RussoPrefactor.lean)
-/
@[path]
private lemma rp_prefactor_pos_eq
  {J β : ℝ}
-- given
  (hJ : 0 < J)
  (hβ : 0 < β) :
-- imply
  0 < J / (Real.exp (β * J) - 1) := by
-- proof
  apply StatMech.OSSS.RussoPrefactor.rp_prefactor_pos hJ hβ

/--
[rp_prefactor_antitone_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RussoPrefactor.lean)
-/
@[path]
private lemma rp_prefactor_antitone_beta_eq
  {J β β₀ : ℝ}
-- given
  (hJ : 0 < J)
  (hβ : 0 < β)
  (hββ : β ≤ β₀) :
-- imply
  J / (Real.exp (β₀ * J) - 1) ≤ J / (Real.exp (β * J) - 1) := by
-- proof
  apply StatMech.OSSS.RussoPrefactor.rp_prefactor_antitone_beta hJ hβ hββ

/--
[rp_minPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RussoPrefactor.lean)
-/
@[path]
private lemma rp_minPrefactor_eq
  [Fintype E]
  [Nonempty E]
  {g : E → ℝ}
-- given
  (hg : ∀ e, 0 < g e) :
-- imply
  ∃ cR : ℝ, 0 < cR ∧ ∀ e, cR ≤ g e := by
-- proof
  apply StatMech.OSSS.RussoPrefactor.rp_minPrefactor g hg

/--
[rp_prefactor_extraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RussoPrefactor.lean)
-/
@[path]
private lemma rp_prefactor_extraction_eq
  [Fintype E]
  {g Cov : E → ℝ}
  {cR : ℝ}
-- given
  (hg : ∀ e, cR ≤ g e)
  (hCov : ∀ e, 0 ≤ Cov e) :
-- imply
  cR * ∑ e, Cov e ≤ ∑ e, g e * Cov e := by
-- proof
  apply StatMech.OSSS.RussoPrefactor.rp_prefactor_extraction g Cov cR hg hCov

/--
[rp_differential_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RussoPrefactor.lean)
-/
@[path]
private lemma rp_differential_lower_eq
  [Fintype E]
  [Nonempty E]
  {g Cov : E → ℝ}
  {θ' : ℝ}
-- given
  (hg : ∀ e, 0 < g e)
  (hCov : ∀ e, 0 ≤ Cov e)
  (hderiv : θ' = ∑ e, g e * Cov e) :
-- imply
  ∃ cR : ℝ, 0 < cR ∧ cR * ∑ e, Cov e ≤ θ' := by
-- proof
  apply StatMech.OSSS.RussoPrefactor.rp_differential_lower g Cov θ' hg hCov hderiv

/--
[rp_differential_lower_weighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RussoPrefactor.lean)
-/
@[path]
private lemma rp_differential_lower_weighted_eq
  [Fintype E]
  [Nonempty E]
  {J Cov : E → ℝ}
  {β θ' : ℝ}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β)
  (hCov : ∀ e, 0 ≤ Cov e)
  (hderiv : θ' = ∑ e, (J e / (Real.exp (β * J e) - 1)) * Cov e) :
-- imply
  ∃ cR : ℝ, 0 < cR ∧ cR * ∑ e, Cov e ≤ θ' := by
-- proof
  apply StatMech.OSSS.RussoPrefactor.rp_differential_lower_weighted J Cov β θ' hJ hβ hCov hderiv

/--
[rp_differential_lower_weighted_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RussoPrefactor.lean)
-/
@[path]
private lemma rp_differential_lower_weighted_beta_eq
  [Fintype E]
  [Nonempty E]
  {J Cov : E → ℝ}
  {β θ' : ℝ}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β)
  (hCov : ∀ e, 0 ≤ Cov e)
  (hderiv : θ' = ∑ e, (J e / (1 - Real.exp (-(β * J e)))) * Cov e) :
-- imply
  ∃ cR : ℝ, 0 < cR ∧ cR * ∑ e, Cov e ≤ θ' := by
-- proof
  apply StatMech.OSSS.RussoPrefactor.rp_differential_lower_weighted_beta J Cov β θ' hJ hβ hCov hderiv

/--
[rp_beta_prefactor_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RussoPrefactor.lean)
-/
@[path]
private lemma rp_beta_prefactor_antitone_eq
  {J β β₀ : ℝ}
-- given
  (hJ : 0 < J)
  (hβ : 0 < β)
  (hββ₀ : β ≤ β₀) :
-- imply
  J / (1 - Real.exp (-(β₀ * J))) ≤ J / (1 - Real.exp (-(β * J))) := by
-- proof
  apply StatMech.OSSS.RussoPrefactor.rp_beta_prefactor_antitone hJ hβ hββ₀

/--
[rp_differential_lower_weighted_beta_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RussoPrefactor.lean)
-/
@[path]
private lemma rp_differential_lower_weighted_beta_uniform_eq
  [Fintype E]
  [Nonempty E]
  {J Cov : E → ℝ}
  {β β₀ θ' : ℝ}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β)
  (hββ₀ : β ≤ β₀)
  (hCov : ∀ e, 0 ≤ Cov e)
  (hderiv : θ' = ∑ e, (J e / (1 - Real.exp (-(β * J e)))) * Cov e) :
-- imply
  ∃ cR : ℝ, 0 < cR ∧ (∀ e, cR ≤ J e / (1 - Real.exp (-(β₀ * J e)))) ∧ cR * ∑ e, Cov e ≤ θ' := by
-- proof
  apply StatMech.OSSS.RussoPrefactor.rp_differential_lower_weighted_beta_uniform J Cov β β₀ θ' hJ hβ hββ₀ hCov hderiv


-- created on 2026-10-23
