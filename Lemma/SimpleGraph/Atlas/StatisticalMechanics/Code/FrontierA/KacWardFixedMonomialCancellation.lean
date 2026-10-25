import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFixedMonomialCancellation.Part2
open StatMech StatMech.FrontierA


/--
[kwLoopOrbitExponent_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFixedMonomialCancellation.lean)
-/
@[path]
private lemma kwLoopOrbitExponent_surgery_eq
  [Fintype Dart]
  [DecidableEq Dart]
  {n : ℕ}
  [NeZero n]
  {selected : Dart}
-- given
  (reverse : Dart -> Dart)
  (hreverse : Function.Involutive reverse)
  (loop : Fin n -> Dart)
  (hboth : (∃ i, loop i = selected) ∧ ∃ j, loop j = reverse selected) :
-- imply
  kwLoopOrbitExponent reverse (StatMech.Onsager.ons_surgery selected reverse loop) = kwLoopOrbitExponent reverse loop := by
-- proof
  apply StatMech.FrontierA.kwLoopOrbitExponent_surgery selected reverse hreverse loop hboth

/--
[kw_fixedOrbitExponent_surgery_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFixedMonomialCancellation.lean)
-/
@[path]
private lemma kw_fixedOrbitExponent_surgery_cancel_eq
  [Fintype Dart]
  [DecidableEq Dart]
  {n : ℕ}
  [NeZero n]
  {transition : Matrix Dart Dart ℂ}
  {selected : Dart}
  {exponent : Sym2 Dart →₀ ℕ}
-- given
  (reverse : Dart -> Dart)
  (hreverse : Function.Involutive reverse)
  (hreverse_ne : reverse selected ≠ selected)
  (hsign : ∀ loop ∈ StatMech.Onsager.ons_loopSetBoth (n := n) selected (reverse selected), StatMech.Onsager.ons_loopWeight transition (StatMech.Onsager.ons_surgery selected reverse loop) = -StatMech.Onsager.ons_loopWeight transition loop) :
-- imply
  (∑ loop ∈ kwFixedOrbitExponentLoops (n := n) selected reverse exponent, StatMech.Onsager.ons_loopWeight transition loop) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_fixedOrbitExponent_surgery_cancel transition selected reverse hreverse hreverse_ne exponent hsign

/--
[kw_fixedOrbitExponent_reversibleTurnMatrix_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFixedMonomialCancellation.lean)
-/
@[path]
private lemma kw_fixedOrbitExponent_reversibleTurnMatrix_cancel_eq
  [Fintype Dart]
  [DecidableEq Dart]
  {n : ℕ}
  [NeZero n]
  {omega : ℂ}
  {selected : Dart}
  {exponent : Sym2 Dart →₀ ℕ}
-- given
  (reverse : Dart -> Dart)
  (hreverse : Function.Involutive reverse)
  (direction : Dart -> Fin 4)
  (hdirection : ∀ dart, direction (reverse dart) = direction dart + 2)
  (homega : omega ≠ 0)
  (homega_sq : omega ^ 2 = Complex.I)
  (edgeFactor : Dart -> Dart -> ℂ)
  (hedgeFactor : ∀ x y, edgeFactor (reverse y) (reverse x) = edgeFactor x y)
  (hreverse_ne : reverse selected ≠ selected) :
-- imply
  (∑ loop ∈ kwFixedOrbitExponentLoops (n := n) selected reverse exponent, StatMech.Onsager.ons_loopWeight (StatMech.Onsager.ons_reversibleTurnMatrix direction omega edgeFactor) loop) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_fixedOrbitExponent_reversibleTurnMatrix_cancel reverse hreverse direction hdirection omega homega homega_sq edgeFactor hedgeFactor selected hreverse_ne exponent

/--
[kw_fixedOrbitExponent_stateWeightedReversibleTurnMatrix_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFixedMonomialCancellation.lean)
-/
@[path]
private lemma kw_fixedOrbitExponent_stateWeightedReversibleTurnMatrix_cancel_eq
  [Fintype Dart]
  [DecidableEq Dart]
  {n : ℕ}
  [NeZero n]
  {omega : ℂ}
  {selected : Dart}
  {exponent : Sym2 Dart →₀ ℕ}
-- given
  (reverse : Dart -> Dart)
  (hreverse : Function.Involutive reverse)
  (direction : Dart -> Fin 4)
  (hdirection : ∀ dart, direction (reverse dart) = direction dart + 2)
  (homega : omega ≠ 0)
  (homega_sq : omega ^ 2 = Complex.I)
  (rowWeight colWeight : Dart -> ℂ)
  (hweight : ∀ dart, rowWeight (reverse dart) * colWeight (reverse dart) = rowWeight dart * colWeight dart)
  (edgeFactor : Dart -> Dart -> ℂ)
  (hedgeFactor : ∀ x y, edgeFactor (reverse y) (reverse x) = edgeFactor x y)
  (hreverse_ne : reverse selected ≠ selected) :
-- imply
  (∑ loop ∈ kwFixedOrbitExponentLoops (n := n) selected reverse exponent, StatMech.Onsager.ons_loopWeight (StatMech.Onsager.ons_stateWeightedReversibleTurnMatrix direction omega rowWeight colWeight edgeFactor) loop) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_fixedOrbitExponent_stateWeightedReversibleTurnMatrix_cancel reverse hreverse direction hdirection omega homega homega_sq rowWeight colWeight hweight edgeFactor hedgeFactor selected hreverse_ne exponent

/--
[kw_fixedOrbitExponent_gauge_reversibleTurnMatrix_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFixedMonomialCancellation.lean)
-/
@[path]
private lemma kw_fixedOrbitExponent_gauge_reversibleTurnMatrix_cancel_eq
  [Fintype Dart]
  [DecidableEq Dart]
  {n : ℕ}
  [NeZero n]
  {omega : ℂ}
  {selected : Dart}
  {exponent : Sym2 Dart →₀ ℕ}
-- given
  (reverse : Dart -> Dart)
  (hreverse : Function.Involutive reverse)
  (direction : Dart -> Fin 4)
  (hdirection : ∀ dart, direction (reverse dart) = direction dart + 2)
  (homega : omega ≠ 0)
  (homega_sq : omega ^ 2 = Complex.I)
  (edgeFactor : Dart -> Dart -> ℂ)
  (hedgeFactor : ∀ x y, edgeFactor (reverse y) (reverse x) = edgeFactor x y)
  (gauge : Dart -> ℂ)
  (hgauge : ∀ dart, gauge dart ≠ 0)
  (hreverse_ne : reverse selected ≠ selected) :
-- imply
  (∑ loop ∈ kwFixedOrbitExponentLoops (n := n) selected reverse exponent, StatMech.Onsager.ons_loopWeight (kwGaugeConjugate gauge (StatMech.Onsager.ons_reversibleTurnMatrix direction omega edgeFactor)) loop) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_fixedOrbitExponent_gauge_reversibleTurnMatrix_cancel reverse hreverse direction hdirection omega homega homega_sq edgeFactor hedgeFactor gauge hgauge selected hreverse_ne exponent


-- created on 2026-10-23
