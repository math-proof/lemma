import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.ABMeanfieldLimit
open Filter Set Topology StatMech StatMech.Sharpness


/--
[abml_meanfield_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABMeanfieldLimit.lean)
-/
@[path]
private lemma abml_meanfield_limit_eq
  {Mn : Nat → Real → Real}
  {M : Real → Real}
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hfinite : ∀ n b, beta ≤ b → 1 - Mn n b ≤ b * deriv (Mn n) b)
  (hdiffFinite : ∀ n b, DifferentiableAt Real (Mn n) b)
  (hconv : ∀ b, beta ≤ b → Tendsto (fun n ↦ Mn n b) atTop (nhds (M b)))
  (hdiff : DifferentiableAt Real M beta) :
-- imply
  1 - M beta ≤ beta * deriv M beta := by
-- proof
  apply StatMech.Sharpness.abml_meanfield_limit Mn M beta hbeta hfinite hdiffFinite hconv hdiff


-- created on 2026-10-23
