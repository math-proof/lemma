import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.ABPhysicalDeriv
open Finset Set StatMech StatMech.Sharpness


/--
[abpd_hasDerivAt_configWeightV_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABPhysicalDeriv.lean)
-/
@[path]
private lemma abpd_hasDerivAt_configWeightV_profile_eq
  [Fintype E]
  [DecidableEq E]
  {r : ℝ → E → ℝ}
  {r' : E → ℝ}
  {t : ℝ}
  {omega : ConfigSpace E}
-- given
  (hr : ∀ e, HasDerivAt (fun u => r u e) (r' e) t) :
-- imply
  HasDerivAt (fun u => configWeightV (r u) omega) (∑ e, (if omega e then r' e else -(r' e)) * weightOffV (r t) e omega) t := by
-- proof
  apply StatMech.Sharpness.abpd_hasDerivAt_configWeightV_profile r r' t hr omega

/--
[abpd_hasDerivAt_probV_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABPhysicalDeriv.lean)
-/
@[path]
private lemma abpd_hasDerivAt_probV_profile_eq
  [Fintype E]
  [DecidableEq E]
  {r : ℝ → E → ℝ}
  {r' : E → ℝ}
  {t : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hr : ∀ e, HasDerivAt (fun u => r u e) (r' e) t)
  (hA : IsIncreasing A) :
-- imply
  HasDerivAt (fun u => probV (r u) A) (∑ e, r' e * pivotalProbV (r t) A e) t := by
-- proof
  apply StatMech.Sharpness.abpd_hasDerivAt_probV_profile r r' t hr A hA

/--
[abpd_hasDerivAt_beta_field_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABPhysicalDeriv.lean)
-/
@[path]
private lemma abpd_hasDerivAt_beta_field_profile_eq
  [Fintype E]
  [DecidableEq E]
  {s : Finset E}
  {q : ℝ}
  {J : E → ℝ}
  {A : Set (ConfigSpace E)}
  {beta : ℝ}
-- given
  (hA : IsIncreasing A) :
-- imply
  HasDerivAt (fun b => probV (abpdBetaFieldParams s q J b) A) (∑ e, (if e ∈ s then 0 else J e * Real.exp (-beta * J e)) * pivotalProbV (abpdBetaFieldParams s q J beta) A e) beta := by
-- proof
  apply StatMech.Sharpness.abpd_hasDerivAt_beta_field_profile s q J A hA beta

/--
[abpd_deriv_beta_field_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABPhysicalDeriv.lean)
-/
@[path]
private lemma abpd_deriv_beta_field_profile_eq
  [Fintype E]
  [DecidableEq E]
  {s : Finset E}
  {q : ℝ}
  {J : E → ℝ}
  {A : Set (ConfigSpace E)}
  {beta : ℝ}
-- given
  (hA : IsIncreasing A) :
-- imply
  deriv (fun b => probV (abpdBetaFieldParams s q J b) A) beta = ∑ e, (if e ∈ s then 0 else J e * Real.exp (-beta * J e)) * pivotalProbV (abpdBetaFieldParams s q J beta) A e := by
-- proof
  apply StatMech.Sharpness.abpd_deriv_beta_field_profile s q J A hA beta

/--
[abpd_deriv_beta_field_profile_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABPhysicalDeriv.lean)
-/
@[path]
private lemma abpd_deriv_beta_field_profile_closed_eq
  [Fintype E]
  [DecidableEq E]
  {s : Finset E}
  {q : ℝ}
  {J : E → ℝ}
  {A : Set (ConfigSpace E)}
  {beta : ℝ}
-- given
  (hA : IsIncreasing A) :
-- imply
  deriv (fun b => probV (abpdBetaFieldParams s q J b) A) beta = ∑ e, if e ∈ s then 0 else J e * probV (abpdBetaFieldParams s q J beta) (abgiClosedPivotal e A) := by
-- proof
  apply StatMech.Sharpness.abpd_deriv_beta_field_profile_closed s q J A hA beta


-- created on 2026-10-23
