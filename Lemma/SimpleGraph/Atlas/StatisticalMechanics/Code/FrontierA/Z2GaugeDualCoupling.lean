import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.Z2GaugeDualCoupling
open Finset StatMech StatMech.FrontierA


/--
[tanh_pos_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDualCoupling.lean)
-/
@[path]
private lemma tanh_pos_of_pos_eq
  [Fintype E]
  [DecidableEq E]
  {K : ℝ}
-- given
  (hK : 0 < K) :
-- imply
  0 < Real.tanh K := by
-- proof
  apply StatMech.FrontierA.tanh_pos_of_pos hK

/--
[gaugeDualCoupling_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDualCoupling.lean)
-/
@[path]
private lemma gaugeDualCoupling_pos_eq
  [Fintype E]
  [DecidableEq E]
  {K : ℝ}
-- given
  (hK : 0 < K) :
-- imply
  0 < gaugeDualCoupling K := by
-- proof
  apply StatMech.FrontierA.gaugeDualCoupling_pos hK

/--
[exp_neg_two_mul_gaugeDualCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDualCoupling.lean)
-/
@[path]
private lemma exp_neg_two_mul_gaugeDualCoupling_eq
  [Fintype E]
  [DecidableEq E]
  {K : ℝ}
-- given
  (hK : 0 < K) :
-- imply
  Real.exp (-2 * gaugeDualCoupling K) = Real.tanh K := by
-- proof
  apply StatMech.FrontierA.exp_neg_two_mul_gaugeDualCoupling hK

/--
[exp_two_mul_gaugeDualCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDualCoupling.lean)
-/
@[path]
private lemma exp_two_mul_gaugeDualCoupling_eq
  [Fintype E]
  [DecidableEq E]
  {K : ℝ}
-- given
  (hK : 0 < K) :
-- imply
  Real.exp (2 * gaugeDualCoupling K) = Real.cosh K / Real.sinh K := by
-- proof
  apply StatMech.FrontierA.exp_two_mul_gaugeDualCoupling hK

/--
[prod_tanh_eq_prod_dualActivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDualCoupling.lean)
-/
@[path]
private lemma prod_tanh_eq_prod_dualActivity_eq
  [Fintype E]
  [DecidableEq E]
  {K : P → ℝ}
  {A : Finset P}
-- given
  (hK : ∀ p, 0 < K p) :
-- imply
  (∏ p ∈ A, Real.tanh (K p)) = ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p)) := by
-- proof
  apply StatMech.FrontierA.prod_tanh_eq_prod_dualActivity K hK A

/--
[gaugeClosedSurfaceSum_eq_dualActivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDualCoupling.lean)
-/
@[path]
private lemma gaugeClosedSurfaceSum_eq_dualActivity_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {K : P → ℝ}
-- given
  (hK : ∀ p, 0 < K p) :
-- imply
  gaugeClosedSurfaceSum incidence K = ∑ A ∈ (Finset.univ : Finset P).powerset.filter (IsClosedPlaquetteSet incidence), ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p)) := by
-- proof
  apply StatMech.FrontierA.gaugeClosedSurfaceSum_eq_dualActivity incidence K hK

/--
[gaugeWilsonSurfaceSum_eq_dualActivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDualCoupling.lean)
-/
@[path]
private lemma gaugeWilsonSurfaceSum_eq_dualActivity_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {K : P → ℝ}
  {L : Finset E}
-- given
  (hK : ∀ p, 0 < K p) :
-- imply
  gaugeWilsonSurfaceSum incidence K L = ∑ A ∈ (Finset.univ : Finset P).powerset.filter (fun A => HasWilsonBoundary incidence A L), ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p)) := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonSurfaceSum_eq_dualActivity incidence K hK L

/--
[gaugePartition_dualActivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDualCoupling.lean)
-/
@[path]
private lemma gaugePartition_dualActivity_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {K : P → ℝ}
-- given
  (hK : ∀ p, 0 < K p) :
-- imply
  gaugePartition incidence K = (2 : ℝ) ^ Fintype.card E * (∏ p : P, Real.cosh (K p)) * ∑ A ∈ (Finset.univ : Finset P).powerset.filter (IsClosedPlaquetteSet incidence), ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p)) := by
-- proof
  apply StatMech.FrontierA.gaugePartition_dualActivity incidence K hK

/--
[gaugeWilsonExpectation_eq_dualActivityRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDualCoupling.lean)
-/
@[path]
private lemma gaugeWilsonExpectation_eq_dualActivityRatio_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {K : P → ℝ}
  {L : Finset E}
-- given
  (hK : ∀ p, 0 < K p) :
-- imply
  gaugeWilsonExpectation incidence K L = (∑ A ∈ (Finset.univ : Finset P).powerset.filter (fun A => HasWilsonBoundary incidence A L), ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p))) / (∑ A ∈ (Finset.univ : Finset P).powerset.filter (IsClosedPlaquetteSet incidence), ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p))) := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonExpectation_eq_dualActivityRatio incidence K hK L


-- created on 2026-10-23
