import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.osd_diffineqpointwise
open StatMech StatMech.Walls


/--
[osd_diff_ineq_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_diffineqpointwise.lean)
-/
@[path]
private lemma osd_diff_ineq_pointwise_eq
  {n : ℕ}
  {c₀ cR D θ θ' S : ℝ}
-- given
  (hD : 0 < D)
  (hcov : (n : ℝ) * c₀ * (θ * (1 - θ)) ≤ D * S)
  (hRusso : cR * S ≤ θ')
  (hcR : 0 ≤ cR) :
-- imply
  (n : ℝ) * c₀ * cR / D * (θ * (1 - θ)) ≤ θ' := by
-- proof
  apply StatMech.Walls.osd_diff_ineq_pointwise n c₀ cR D θ θ' S hD hcov hRusso hcR

/--
[osd_diff_ineq_pointwise_eq_dep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_diffineqpointwise.lean)
-/
@[path]
private lemma osd_diff_ineq_pointwise_eq_dep_eq :
-- imply
  @osd_diff_ineq_pointwise = @StatMech.OSSS.SharpnessFK.differential_inequality := by
-- proof
  apply StatMech.Walls.osd_diff_ineq_pointwise_eq_dep

/--
[osd_diff_ineq_pointwise_direct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_diffineqpointwise.lean)
-/
@[path]
private lemma osd_diff_ineq_pointwise_direct_eq
  {n : ℕ}
  {c₀ cR D θ θ' S : ℝ}
-- given
  (hD : 0 < D)
  (hcov : (n : ℝ) * c₀ * (θ * (1 - θ)) ≤ D * S)
  (hRusso : cR * S ≤ θ')
  (hcR : 0 ≤ cR) :
-- imply
  (n : ℝ) * c₀ * cR / D * (θ * (1 - θ)) ≤ θ' := by
-- proof
  apply StatMech.Walls.osd_diff_ineq_pointwise_direct n c₀ cR D θ θ' S hD hcov hRusso hcR


-- created on 2026-10-23
