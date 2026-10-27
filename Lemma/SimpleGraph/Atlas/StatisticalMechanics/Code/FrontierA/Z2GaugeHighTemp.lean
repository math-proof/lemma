import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeHighTemp
open Finset StatMech StatMech.FrontierA


/--
[plaquetteIncidenceCount_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean)
-/
@[path]
private lemma plaquetteIncidenceCount_empty_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
-- given
  (incidence : P -> Finset E) :
-- imply
  plaquetteIncidenceCount incidence (∅ : Finset P) e = 0 := by
-- proof
  apply StatMech.FrontierA.plaquetteIncidenceCount_empty incidence e

/--
[plaquetteIncidenceCount_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean)
-/
@[path]
private lemma plaquetteIncidenceCount_insert_eq
  [Fintype E]
  [DecidableEq E]
  {p : P}
  {A : Finset P}
  {e : E}
-- given
  (incidence : P -> Finset E)
  (hp : p ∉ A) :
-- imply
  plaquetteIncidenceCount incidence (insert p A) e = (if e ∈ incidence p then 1 else 0) + plaquetteIncidenceCount incidence A e := by
-- proof
  apply StatMech.FrontierA.plaquetteIncidenceCount_insert incidence hp e

/--
[hasWilsonBoundary_empty_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean)
-/
@[path]
private lemma hasWilsonBoundary_empty_iff_eq
  [Fintype E]
  [DecidableEq E]
  {A : Finset P}
-- given
  (incidence : P -> Finset E) :
-- imply
  HasWilsonBoundary incidence A (∅ : Finset E) ↔ IsClosedPlaquetteSet incidence A := by
-- proof
  apply StatMech.FrontierA.hasWilsonBoundary_empty_iff incidence A

/--
[gaugeEdgeSpin_eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean)
-/
@[path]
private lemma gaugeEdgeSpin_eq_one_or_neg_one_eq
  [Fintype E]
  [DecidableEq E]
  {omega : GaugeConfig E}
  {e : E} :
-- imply
  gaugeEdgeSpin omega e = 1 ∨ gaugeEdgeSpin omega e = -1 := by
-- proof
  apply StatMech.FrontierA.gaugeEdgeSpin_eq_one_or_neg_one omega e

/--
[gaugeEdgeSpin_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean)
-/
@[path]
private lemma gaugeEdgeSpin_sq_eq
  [Fintype E]
  [DecidableEq E]
  {omega : GaugeConfig E}
  {e : E} :
-- imply
  gaugeEdgeSpin omega e ^ 2 = 1 := by
-- proof
  apply StatMech.FrontierA.gaugeEdgeSpin_sq omega e

/--
[sum_gaugeEdgeSpin_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean)
-/
@[path]
private lemma sum_gaugeEdgeSpin_pow_eq
  [Fintype E]
  [DecidableEq E]
  {m : Nat} :
-- imply
  (∑ b : Bool, (if b then (1 : ℝ) else -1) ^ m) = if Even m then 2 else 0 := by
-- proof
  apply StatMech.FrontierA.sum_gaugeEdgeSpin_pow m

/--
[sum_gaugeEdgeSpin_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean)
-/
@[path]
private lemma sum_gaugeEdgeSpin_monomial_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (m : E -> Nat) :
-- imply
  (∑ omega : GaugeConfig E, ∏ e : E, (gaugeEdgeSpin omega e) ^ (m e)) = if (∀ e, Even (m e)) then (2 : ℝ) ^ Fintype.card E else 0 := by
-- proof
  apply StatMech.FrontierA.sum_gaugeEdgeSpin_monomial m

/--
[plaquetteSpin_eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean)
-/
@[path]
private lemma plaquetteSpin_eq_one_or_neg_one_eq
  [Fintype E]
  [DecidableEq E]
  {omega : GaugeConfig E}
  {p : P}
-- given
  (incidence : P -> Finset E) :
-- imply
  plaquetteSpin incidence omega p = 1 ∨ plaquetteSpin incidence omega p = -1 := by
-- proof
  apply StatMech.FrontierA.plaquetteSpin_eq_one_or_neg_one incidence omega p

/--
[prod_plaquetteSpin_eq_prod_incidence_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean)
-/
@[path]
private lemma prod_plaquetteSpin_eq_prod_incidence_pow_eq
  [Fintype E]
  [DecidableEq E]
  {omega : GaugeConfig E}
  {A : Finset P}
-- given
  (incidence : P -> Finset E) :
-- imply
  (∏ p ∈ A, plaquetteSpin incidence omega p) = ∏ e : E, (gaugeEdgeSpin omega e) ^ (plaquetteIncidenceCount incidence A e) := by
-- proof
  apply StatMech.FrontierA.prod_plaquetteSpin_eq_prod_incidence_pow incidence omega A

/--
[sum_prod_plaquetteSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean)
-/
@[path]
private lemma sum_prod_plaquetteSpin_eq
  [Fintype E]
  [DecidableEq E]
  {A : Finset P}
-- given
  (incidence : P -> Finset E) :
-- imply
  (∑ omega : GaugeConfig E, ∏ p ∈ A, plaquetteSpin incidence omega p) = if IsClosedPlaquetteSet incidence A then (2 : ℝ) ^ Fintype.card E else 0 := by
-- proof
  apply StatMech.FrontierA.sum_prod_plaquetteSpin incidence A

/--
[wilsonSpin_eq_prod_indicator_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean)
-/
@[path]
private lemma wilsonSpin_eq_prod_indicator_pow_eq
  [Fintype E]
  [DecidableEq E]
  {L : Finset E}
  {omega : GaugeConfig E} :
-- imply
  wilsonSpin L omega = ∏ e : E, (gaugeEdgeSpin omega e) ^ (if e ∈ L then 1 else 0) := by
-- proof
  apply StatMech.FrontierA.wilsonSpin_eq_prod_indicator_pow L omega

/--
[sum_wilson_mul_prod_plaquetteSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean)
-/
@[path]
private lemma sum_wilson_mul_prod_plaquetteSpin_eq
  [Fintype E]
  [DecidableEq E]
  {A : Finset P}
  {L : Finset E}
-- given
  (incidence : P -> Finset E) :
-- imply
  (∑ omega : GaugeConfig E, wilsonSpin L omega * ∏ p ∈ A, plaquetteSpin incidence omega p) = if HasWilsonBoundary incidence A L then (2 : ℝ) ^ Fintype.card E else 0 := by
-- proof
  apply StatMech.FrontierA.sum_wilson_mul_prod_plaquetteSpin incidence A L

/--
[gaugeWeight_eq_highTempFactors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean)
-/
@[path]
private lemma gaugeWeight_eq_highTempFactors_eq
  [Fintype E]
  [DecidableEq E]
  {omega : GaugeConfig E}
-- given
  (incidence : P -> Finset E)
  (K : P -> ℝ) :
-- imply
  gaugeWeight incidence K omega = (∏ p : P, Real.cosh (K p)) * ∏ p : P, (1 + Real.tanh (K p) * plaquetteSpin incidence omega p) := by
-- proof
  apply StatMech.FrontierA.gaugeWeight_eq_highTempFactors incidence K omega

/--
[gaugePartition_highTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean)
-/
@[path]
private lemma gaugePartition_highTemp_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (incidence : P -> Finset E)
  (K : P -> ℝ) :
-- imply
  gaugePartition incidence K = (2 : ℝ) ^ Fintype.card E * (∏ p : P, Real.cosh (K p)) * ∑ A ∈ (Finset.univ : Finset P).powerset.filter (IsClosedPlaquetteSet incidence), ∏ p ∈ A, Real.tanh (K p) := by
-- proof
  apply StatMech.FrontierA.gaugePartition_highTemp incidence K

/--
[gaugeWilsonNumerator_highTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean)
-/
@[path]
private lemma gaugeWilsonNumerator_highTemp_eq
  [Fintype E]
  [DecidableEq E]
  {L : Finset E}
-- given
  (incidence : P -> Finset E)
  (K : P -> ℝ) :
-- imply
  gaugeWilsonNumerator incidence K L = (2 : ℝ) ^ Fintype.card E * (∏ p : P, Real.cosh (K p)) * ∑ A ∈ (Finset.univ : Finset P).powerset.filter (fun A => HasWilsonBoundary incidence A L), ∏ p ∈ A, Real.tanh (K p) := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonNumerator_highTemp incidence K L


-- created on 2026-10-23
