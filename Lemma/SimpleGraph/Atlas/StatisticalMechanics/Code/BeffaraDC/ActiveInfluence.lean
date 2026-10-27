import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.ActiveInfluence.Part2
open StatMech StatMech.BeffaraDC


/--
[activeWeight_open_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluence.lean)
-/
@[path]
private lemma activeWeight_open_pair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : G.edgeSet}
  {ω : ConfigSpace G.edgeSet}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  p * activeWeight G (fun _ => p) q (setClosed e ω) ≤ q * (1 - p) * activeWeight G (fun _ => p) q (setOpen e ω) := by
-- proof
  apply StatMech.BeffaraDC.activeWeight_open_pair G hp hp1 hq e ω

/--
[openMarginal_lower_of_open_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluence.lean)
-/
@[path]
private lemma openMarginal_lower_of_open_pair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {e : E}
  {p q : ℝ}
-- given
  (hμ1 : ∑ ω, μ ω = 1)
  (hden : 0 < p + q * (1 - p))
  (hpair : ∀ ψ, p * μ (setClosed e ψ) ≤ q * (1 - p) * μ (setOpen e ψ)) :
-- imply
  p / (p + q * (1 - p)) ≤ openMarginal μ e := by
-- proof
  apply StatMech.BeffaraDC.openMarginal_lower_of_open_pair G μ hμ1 e hden hpair

/--
[active_reducedDensity_le_openMarginal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluence.lean)
-/
@[path]
private lemma active_reducedDensity_le_openMarginal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : G.edgeSet}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  reducedDensity p q ≤ openMarginal (activeProb G (fun _ => p) q) e := by
-- proof
  apply StatMech.BeffaraDC.active_reducedDensity_le_openMarginal G hp hp1 hq e

/--
[activeInfluence_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluence.lean)
-/
@[path]
private lemma activeInfluence_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace G.edgeSet)}
  {e : G.edgeSet}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  0 ≤ activeInfluence G p q A e := by
-- proof
  apply StatMech.BeffaraDC.activeInfluence_nonneg G hp hp1 hq A hA e

/--
[activeCov_eq_marginal_mul_influence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluence.lean)
-/
@[path]
private lemma activeCov_eq_marginal_mul_influence_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace G.edgeSet)}
  {e : G.edgeSet}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  activeCov G (fun _ => p) q (A.indicator fun _ => (1 : ℝ)) (OSSS.Lindeberg.coord e) = openMarginal (activeProb G (fun _ => p) q) e * (1 - openMarginal (activeProb G (fun _ => p) q) e) * activeInfluence G p q A e := by
-- proof
  apply StatMech.BeffaraDC.activeCov_eq_marginal_mul_influence G hp hp1 hq A e

/--
[active_deriv_ge_total_influence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluence.lean)
-/
@[path]
private lemma active_deriv_ge_total_influence_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q ε : ℝ}
  {A : Set (ConfigSpace G.edgeSet)}
-- given
  (hε : 0 < ε)
  (hp0 : ε ≤ p)
  (hp1 : p ≤ 1 - ε)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (ε ^ 2 / q) * (∑ e : G.edgeSet, activeInfluence G p q A e) ≤ deriv (fun x => activeProbOf G (fun _ => x) q A) p := by
-- proof
  apply StatMech.BeffaraDC.active_deriv_ge_total_influence G hε hp0 hp1 hq A hA


-- created on 2026-10-23
