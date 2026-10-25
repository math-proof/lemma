import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.ActiveEdgeRussoP
open Finset StatMech StatMech.FK


/--
[centeredScore_extendActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdgeRussoP.lean)
-/
@[path]
private lemma centeredScore_extendActive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {ω : ConfigSpace G.edgeSet} :
-- imply
  (∑ e ∈ G.edgeFinset, (coord e (extendActive G ω) - p)) = activePScore G p ω := by
-- proof
  apply StatMech.FK.centeredScore_extendActive G p ω

/--
[hasDerivAt_activeWeight_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdgeRussoP.lean)
-/
@[path]
private lemma hasDerivAt_activeWeight_p_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {q : ℝ}
  {ω : ConfigSpace G.edgeSet}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  HasDerivAt (fun x => activeWeight G (fun _ => x) q ω) (activeWeight G (fun _ => p) q ω * activePScore G p ω / (p * (1 - p))) p := by
-- proof
  apply StatMech.FK.hasDerivAt_activeWeight_p G hp hp1 q ω

/--
[hasDerivAt_activeNumer_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdgeRussoP.lean)
-/
@[path]
private lemma hasDerivAt_activeNumer_p_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {q : ℝ}
  {f : ConfigSpace G.edgeSet → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  HasDerivAt (fun x => activeNumer G (fun _ => x) q f) (activeNumer G (fun _ => p) q (fun ω => f ω * activePScore G p ω) / (p * (1 - p))) p := by
-- proof
  apply StatMech.FK.hasDerivAt_activeNumer_p G hp hp1 q f

/--
[hasDerivAt_activeMean_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdgeRussoP.lean)
-/
@[path]
private lemma hasDerivAt_activeMean_p_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {q : ℝ}
  {f : ConfigSpace G.edgeSet → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  HasDerivAt (fun x => activeMean G (fun _ => x) q f) ((∑ e : G.edgeSet, activeCov G (fun _ => p) q f (OSSS.Lindeberg.coord e)) / (p * (1 - p))) p := by
-- proof
  apply StatMech.FK.hasDerivAt_activeMean_p G hp hp1 hq f

/--
[hasDerivAt_activeProbOf_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdgeRussoP.lean)
-/
@[path]
private lemma hasDerivAt_activeProbOf_p_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {q : ℝ}
  {A : Set (ConfigSpace G.edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  HasDerivAt (fun x => activeProbOf G (fun _ => x) q A) ((∑ e : G.edgeSet, activeCov G (fun _ => p) q (A.indicator fun _ => (1 : ℝ)) (OSSS.Lindeberg.coord e)) / (p * (1 - p))) p := by
-- proof
  apply StatMech.FK.hasDerivAt_activeProbOf_p G hp hp1 hq A


-- created on 2026-10-23
