import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearGraphCancellation
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[kwGraphNonbacktrackingFactor_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearGraphCancellation.lean)
-/
@[path]
private lemma kwGraphNonbacktrackingFactor_reverse_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {dart next : G.Dart} :
-- imply
  kwGraphNonbacktrackingFactor G next.symm dart.symm = kwGraphNonbacktrackingFactor G dart next := by
-- proof
  apply StatMech.FrontierA.kwGraphNonbacktrackingFactor_reverse G dart next

/--
[kwGraphTransition_turnW_eq_stateWeighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearGraphCancellation.lean)
-/
@[path]
private lemma kwGraphTransition_turnW_eq_stateWeighted_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {omega : ℂ}
-- given
  (weight : Sym2 V -> ℂ)
  (direction : G.Dart -> Fin 4) :
-- imply
  kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart)) = StatMech.Onsager.ons_stateWeightedReversibleTurnMatrix direction omega (fun dart => weight dart.edge) (fun _ => 1) (kwGraphNonbacktrackingFactor G) := by
-- proof
  apply StatMech.FrontierA.kwGraphTransition_turnW_eq_stateWeighted G weight direction omega

/--
[kw_rectilinearGraph_fixedOrbitExponent_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearGraphCancellation.lean)
-/
@[path]
private lemma kw_rectilinearGraph_fixedOrbitExponent_cancel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {omega : ℂ}
  {selected : G.Dart}
  {exponent : Sym2 G.Dart →₀ ℕ}
-- given
  (weight : Sym2 V -> ℂ)
  (direction : G.Dart -> Fin 4)
  (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
  (homega : omega ≠ 0)
  (homega_sq : omega ^ 2 = Complex.I) :
-- imply
  (∑ loop ∈ kwFixedOrbitExponentLoops (n := n) selected SimpleGraph.Dart.symm exponent, StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart))) loop) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_rectilinearGraph_fixedOrbitExponent_cancel G weight direction hdirection omega homega homega_sq selected exponent

/--
[kw_rectilinearGraph_fixedOrbitExponent_gauge_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearGraphCancellation.lean)
-/
@[path]
private lemma kw_rectilinearGraph_fixedOrbitExponent_gauge_cancel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {omega : ℂ}
  {selected : G.Dart}
  {exponent : Sym2 G.Dart →₀ ℕ}
-- given
  (weight : Sym2 V -> ℂ)
  (direction : G.Dart -> Fin 4)
  (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
  (homega : omega ≠ 0)
  (homega_sq : omega ^ 2 = Complex.I)
  (gauge : G.Dart -> ℂ)
  (hgauge : ∀ dart, gauge dart ≠ 0) :
-- imply
  (∑ loop ∈ kwFixedOrbitExponentLoops (n := n) selected SimpleGraph.Dart.symm exponent, StatMech.Onsager.ons_loopWeight (kwGaugeConjugate gauge (kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart)))) loop) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_rectilinearGraph_fixedOrbitExponent_gauge_cancel G weight direction hdirection omega homega homega_sq gauge hgauge selected exponent


-- created on 2026-10-23
