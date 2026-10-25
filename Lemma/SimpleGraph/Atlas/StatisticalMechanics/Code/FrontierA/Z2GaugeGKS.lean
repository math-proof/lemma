import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeGKS.Part2
open Finset StatMech StatMech.FrontierA


/--
[gaugeEdgeSpin_xnor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma gaugeEdgeSpin_xnor_eq
  [Fintype E]
  [DecidableEq E]
  {sigma q : GaugeConfig E}
  {e : E} :
-- imply
  gaugeEdgeSpin (StatMech.Ising.xnor sigma q) e = gaugeEdgeSpin sigma e * gaugeEdgeSpin q e := by
-- proof
  apply StatMech.FrontierA.gaugeEdgeSpin_xnor sigma q e

/--
[plaquetteSpin_xnor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma plaquetteSpin_xnor_eq
  [Fintype E]
  [DecidableEq E]
  {sigma q : GaugeConfig E}
  {p : P}
-- given
  (incidence : P -> Finset E) :
-- imply
  plaquetteSpin incidence (StatMech.Ising.xnor sigma q) p = plaquetteSpin incidence sigma p * plaquetteSpin incidence q p := by
-- proof
  apply StatMech.FrontierA.plaquetteSpin_xnor incidence sigma q p

/--
[wilsonSpin_xnor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma wilsonSpin_xnor_eq
  [Fintype E]
  [DecidableEq E]
  {L : Finset E}
  {sigma q : GaugeConfig E} :
-- imply
  wilsonSpin L (StatMech.Ising.xnor sigma q) = wilsonSpin L sigma * wilsonSpin L q := by
-- proof
  apply StatMech.FrontierA.wilsonSpin_xnor L sigma q

/--
[wilsonSpin_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma wilsonSpin_mul_self_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Finset E}
  {sigma : GaugeConfig E} :
-- imply
  wilsonSpin A sigma * wilsonSpin B sigma = wilsonSpin (A ∆ B) sigma := by
-- proof
  apply StatMech.FrontierA.wilsonSpin_mul_self A B sigma

/--
[isSpinMonomial_plaquetteSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma isSpinMonomial_plaquetteSpin_eq
  [Fintype E]
  [DecidableEq E]
  {p : P}
-- given
  (incidence : P -> Finset E) :
-- imply
  StatMech.Ising.IsSpinMonomial (fun sigma => plaquetteSpin incidence sigma p) := by
-- proof
  apply StatMech.FrontierA.isSpinMonomial_plaquetteSpin incidence p

/--
[isSpinMonomial_wilsonSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma isSpinMonomial_wilsonSpin_eq
  [Fintype E]
  [DecidableEq E]
  {L : Finset E} :
-- imply
  StatMech.Ising.IsSpinMonomial (wilsonSpin L : GaugeConfig E -> Real) := by
-- proof
  apply StatMech.FrontierA.isSpinMonomial_wilsonSpin L

/--
[one_add_plaquetteSpin_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma one_add_plaquetteSpin_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {q : GaugeConfig E}
  {p : P}
-- given
  (incidence : P -> Finset E) :
-- imply
  0 <= 1 + plaquetteSpin incidence q p := by
-- proof
  apply StatMech.FrontierA.one_add_plaquetteSpin_nonneg incidence q p

/--
[one_sub_wilsonSpin_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma one_sub_wilsonSpin_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {L : Finset E}
  {q : GaugeConfig E} :
-- imply
  0 <= 1 - wilsonSpin L q := by
-- proof
  apply StatMech.FrontierA.one_sub_wilsonSpin_nonneg L q

/--
[gaugeWeight_mul_xnor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma gaugeWeight_mul_xnor_eq
  [Fintype E]
  [DecidableEq E]
  {sigma q : GaugeConfig E}
-- given
  (incidence : P -> Finset E)
  (K : P -> Real) :
-- imply
  gaugeWeight incidence K sigma * gaugeWeight incidence K (StatMech.Ising.xnor sigma q) = gaugeWeight incidence (fun p => K p * (1 + plaquetteSpin incidence q p)) sigma := by
-- proof
  apply StatMech.FrontierA.gaugeWeight_mul_xnor incidence K sigma q

/--
[gauge_monomial_weight_sum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma gauge_monomial_weight_sum_nonneg_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (incidence : P -> Finset E)
  (K : P -> Real)
  (hK : forall p, 0 <= K p)
  (obs : GaugeConfig E -> Real)
  (hobs : StatMech.Ising.IsSpinMonomial obs) :
-- imply
  0 <= ∑ sigma : GaugeConfig E, obs sigma * gaugeWeight incidence K sigma := by
-- proof
  apply StatMech.FrontierA.gauge_monomial_weight_sum_nonneg incidence K hK obs hobs

/--
[gauge_inner_q_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma gauge_inner_q_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Finset E}
  {q : GaugeConfig E}
-- given
  (incidence : P -> Finset E)
  (K : P -> Real)
  (hK : forall p, 0 <= K p) :
-- imply
  0 <= ∑ sigma : GaugeConfig E, (wilsonSpin (A ∆ B) sigma * gaugeWeight incidence K sigma * gaugeWeight incidence K (StatMech.Ising.xnor sigma q) - wilsonSpin A sigma * gaugeWeight incidence K sigma * (wilsonSpin B (StatMech.Ising.xnor sigma q) * gaugeWeight incidence K (StatMech.Ising.xnor sigma q))) := by
-- proof
  apply StatMech.FrontierA.gauge_inner_q_nonneg incidence K hK A B q

/--
[gaugeWilsonNumerator_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma gaugeWilsonNumerator_mul_le_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Finset E}
-- given
  (incidence : P -> Finset E)
  (K : P -> Real)
  (hK : forall p, 0 <= K p) :
-- imply
  gaugeWilsonNumerator incidence K A * gaugeWilsonNumerator incidence K B <= gaugeWilsonNumerator incidence K (A ∆ B) * gaugePartition incidence K := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonNumerator_mul_le incidence K hK A B

/--
[gaugeWilsonExpectation_mul_le_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma gaugeWilsonExpectation_mul_le_symmDiff_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Finset E}
-- given
  (incidence : P -> Finset E)
  (K : P -> Real)
  (hK : forall p, 0 <= K p) :
-- imply
  gaugeWilsonExpectation incidence K A * gaugeWilsonExpectation incidence K B <= gaugeWilsonExpectation incidence K (A ∆ B) := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonExpectation_mul_le_symmDiff incidence K hK A B

/--
[gaugeAction_addPlaquetteCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma gaugeAction_addPlaquetteCoupling_eq
  [Fintype E]
  [DecidableEq E]
  {p : P}
  {delta : Real}
  {sigma : GaugeConfig E}
-- given
  (incidence : P -> Finset E)
  (K : P -> Real) :
-- imply
  gaugeAction incidence (addGaugePlaquetteCoupling K p delta) sigma = gaugeAction incidence K sigma + delta * plaquetteSpin incidence sigma p := by
-- proof
  apply StatMech.FrontierA.gaugeAction_addPlaquetteCoupling incidence K p delta sigma

/--
[gaugeWeight_addPlaquetteCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma gaugeWeight_addPlaquetteCoupling_eq
  [Fintype E]
  [DecidableEq E]
  {p : P}
  {delta : Real}
  {sigma : GaugeConfig E}
-- given
  (incidence : P -> Finset E)
  (K : P -> Real) :
-- imply
  gaugeWeight incidence (addGaugePlaquetteCoupling K p delta) sigma = gaugeWeight incidence K sigma * (Real.cosh delta + plaquetteSpin incidence sigma p * Real.sinh delta) := by
-- proof
  apply StatMech.FrontierA.gaugeWeight_addPlaquetteCoupling incidence K p delta sigma

/--
[gaugeWilsonNumerator_addPlaquetteCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma gaugeWilsonNumerator_addPlaquetteCoupling_eq
  [Fintype E]
  [DecidableEq E]
  {p : P}
  {delta : Real}
  {L : Finset E}
-- given
  (incidence : P -> Finset E)
  (K : P -> Real) :
-- imply
  gaugeWilsonNumerator incidence (addGaugePlaquetteCoupling K p delta) L = Real.cosh delta * gaugeWilsonNumerator incidence K L + Real.sinh delta * gaugeWilsonNumerator incidence K (L ∆ incidence p) := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonNumerator_addPlaquetteCoupling incidence K p delta L

/--
[gaugePartition_addPlaquetteCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma gaugePartition_addPlaquetteCoupling_eq
  [Fintype E]
  [DecidableEq E]
  {p : P}
  {delta : Real}
-- given
  (incidence : P -> Finset E)
  (K : P -> Real) :
-- imply
  gaugePartition incidence (addGaugePlaquetteCoupling K p delta) = Real.cosh delta * gaugePartition incidence K + Real.sinh delta * gaugeWilsonNumerator incidence K (incidence p) := by
-- proof
  apply StatMech.FrontierA.gaugePartition_addPlaquetteCoupling incidence K p delta

/--
[gaugeWilsonExpectation_le_addPlaquetteCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma gaugeWilsonExpectation_le_addPlaquetteCoupling_eq
  [Fintype E]
  [DecidableEq E]
  {p : P}
  {delta : Real}
  {L : Finset E}
-- given
  (incidence : P -> Finset E)
  (K : P -> Real)
  (hK : forall q, 0 <= K q)
  (hdelta : 0 <= delta) :
-- imply
  gaugeWilsonExpectation incidence K L <= gaugeWilsonExpectation incidence (addGaugePlaquetteCoupling K p delta) L := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonExpectation_le_addPlaquetteCoupling incidence K hK p hdelta L

/--
[gaugeWilsonExpectation_mono_coupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean)
-/
@[path]
private lemma gaugeWilsonExpectation_mono_coupling_eq
  [Fintype E]
  [DecidableEq E]
  {L : Finset E}
-- given
  (incidence : P -> Finset E)
  (K K' : P -> Real)
  (hK : forall p, 0 <= K p)
  (hKK' : forall p, K p <= K' p) :
-- imply
  gaugeWilsonExpectation incidence K L <= gaugeWilsonExpectation incidence K' L := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonExpectation_mono_coupling incidence K K' hK hKK' L


-- created on 2026-10-23
