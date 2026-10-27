import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterMatchingCutCurrent.Part3
open Finset StatMech StatMech.Ising


/--
[lpMatchingCurrentSkewPolynomial_expanded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterMatchingCutCurrent.lean)
-/
@[path]
private lemma lpMatchingCurrentSkewPolynomial_expanded_eq
  [Fintype W]
  [DecidableEq W]
  {A B C D E Z : Real} :
-- imply
  lpMatchingCurrentSkewPolynomial A B C D E Z = E * Z ^ 4 - D * C * Z ^ 3 - 2 * A * B * Z ^ 3 + 2 * A ^ 2 * C * Z ^ 2 - E * C ^ 2 * Z ^ 2 + D * C ^ 3 * Z - 2 * A * B * C ^ 2 * Z + 2 * B ^ 2 * C * Z ^ 2 := by
-- proof
  apply StatMech.Ising.lpMatchingCurrentSkewPolynomial_expanded A B C D E Z

/--
[lpFiveCurrentSourceMass_eq_sourceTriple_mul_sourcePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterMatchingCutCurrent.lean)
-/
@[path]
private lemma lpFiveCurrentSourceMass_eq_sourceTriple_mul_sourcePair_eq
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : Real}
  {S1 S2 S3 S4 S5 : Finset W}
-- given
  (J : Sym2 W -> Real) :
-- imply
  lpFiveCurrentSourceMass G beta J S1 S2 S3 S4 S5 = sourceTripleSum G beta J S1 S2 S3 * sourcePairSum G beta J S4 S5 := by
-- proof
  apply StatMech.Ising.lpFiveCurrentSourceMass_eq_sourceTriple_mul_sourcePair G beta J S1 S2 S3 S4 S5

/--
[lpMatchingFiveCurrentCoefficient_commonSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterMatchingCutCurrent.lean)
-/
@[path]
private lemma lpMatchingFiveCurrentCoefficient_commonSource_eq
  [Fintype W]
  [DecidableEq W]
  {Si Sj T : Finset W} :
-- imply
  lpFiveSourceTotal (Si ∆ Sj ∆ T) ∅ ∅ ∅ ∅ = Si ∆ Sj ∆ T ∧ lpFiveSourceTotal (Si ∆ Sj) T ∅ ∅ ∅ = Si ∆ Sj ∆ T ∧ lpFiveSourceTotal Si (Sj ∆ T) ∅ ∅ ∅ = Si ∆ Sj ∆ T ∧ lpFiveSourceTotal Si Sj T ∅ ∅ = Si ∆ Sj ∆ T ∧ lpFiveSourceTotal (Si ∆ Sj ∆ T) T T ∅ ∅ = Si ∆ Sj ∆ T ∧ lpFiveSourceTotal (Si ∆ Sj) T T T ∅ = Si ∆ Sj ∆ T ∧ lpFiveSourceTotal Si (Sj ∆ T) T T ∅ = Si ∆ Sj ∆ T ∧ lpFiveSourceTotal (Si ∆ T) (Sj ∆ T) T ∅ ∅ = Si ∆ Sj ∆ T := by
-- proof
  apply StatMech.Ising.lpMatchingFiveCurrentCoefficient_commonSource Si Sj T

/--
[lpMatchingCurrentSkewPolynomial_eq_sum_fiveCurrentCoefficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterMatchingCutCurrent.lean)
-/
@[path]
private lemma lpMatchingCurrentSkewPolynomial_eq_sum_fiveCurrentCoefficient_eq
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : Real}
  {g0 g1 : W}
-- given
  (J : Sym2 W -> Real)
  (left right : I -> W) :
-- imply
  lpMatchingCurrentSkewPolynomial (lpMatchingCurrentA G beta J left right) (lpMatchingCurrentB G beta J left right g0 g1) (lpMatchingCurrentC G beta J g0 g1) (lpMatchingCurrentD G beta J left right) (lpMatchingCurrentE G beta J left right g0 g1) (lpMatchingCurrentZ G beta J) = ∑ i : I, ∑ j : I, lpMatchingFiveCurrentCoefficient G beta J left right g0 g1 i j := by
-- proof
  apply StatMech.Ising.lpMatchingCurrentSkewPolynomial_eq_sum_fiveCurrentCoefficient G beta J left right g0 g1

/--
[lpMatching_centeredGhostCovariance_eq_currentPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterMatchingCutCurrent.lean)
-/
@[path]
private lemma lpMatching_centeredGhostCovariance_eq_currentPolynomial_eq
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : Real}
  {g0 g1 : W}
-- given
  (J : Sym2 W -> Real)
  (left right : I -> W) :
-- imply
  let a := ∑ i : I, expectationJ G beta J (lpMatchingSeamSource left right i) let b := ∑ i : I, expectationJ G beta J (lpMatchingSeamSource left right i ∆ lpMatchingGhostSource g0 g1) let c := expectationJ G beta J (lpMatchingGhostSource g0 g1) let d := ∑ i : I, ∑ j : I, expectationJ G beta J (lpMatchingSeamSource left right i ∆ lpMatchingSeamSource left right j) let e := ∑ i : I, ∑ j : I, expectationJ G beta J (lpMatchingSeamSource left right i ∆ lpMatchingSeamSource left right j ∆ lpMatchingGhostSource g0 g1) let A := lpMatchingCurrentA G beta J left right let B := lpMatchingCurrentB G beta J left right g0 g1 let C := lpMatchingCurrentC G beta J g0 g1 let D := lpMatchingCurrentD G beta J left right let E := lpMatchingCurrentE G beta J left right g0 g1 let Z := lpMatchingCurrentZ G beta J (1 - c ^ 2) * ((e - d * c) - 2 * a * (b - a * c)) + 2 * c * (b - a * c) ^ 2 = lpMatchingCurrentSkewPolynomial A B C D E Z / Z ^ 5 := by
-- proof
  apply StatMech.Ising.lpMatching_centeredGhostCovariance_eq_currentPolynomial G beta J left right g0 g1


-- created on 2026-10-23
