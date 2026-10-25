import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalFourthOrder.Part2
open StatMech StatMech.Universality


/--
[taylorWithinEval_three_eq_cubic_of_contDiffAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalFourthOrder.lean)
-/
@[path]
private lemma taylorWithinEval_three_eq_cubic_of_contDiffAt_eq
  {s : Real}
-- given
  (g : Real -> Real)
  (hs : s ≠ 0)
  (hg0 : ContDiffAt Real 4 g 0) :
-- imply
  taylorWithinEval g 3 (uIcc 0 s) 0 s = cubicTaylorPolynomial g s := by
-- proof
  apply StatMech.Universality.taylorWithinEval_three_eq_cubic_of_contDiffAt g s hs hg0

/--
[cubicTaylor_remainder_le_of_contDiffOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalFourthOrder.lean)
-/
@[path]
private lemma cubicTaylor_remainder_le_of_contDiffOn_eq
  {s M : Real}
-- given
  (g : Real -> Real)
  (hs : s ≠ 0)
  (hg0 : ContDiffAt Real 4 g 0)
  (hg : ContDiffOn Real 4 g (uIcc 0 s))
  (hM : forall t, t ∈ uIcc 0 s -> |iteratedDeriv 4 g t| <= M) :
-- imply
  |g s - cubicTaylorPolynomial g s| <= M * |s| ^ 4 / 24 := by
-- proof
  apply StatMech.Universality.cubicTaylor_remainder_le_of_contDiffOn g s M hs hg0 hg hM

/--
[CenteredFourthOrderSegmentData.ofContDiffOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalFourthOrder.lean)
-/
@[path]
private lemma ofContDiffOn_eq
  {g : Real -> Real}
  {h M : Real}
  {U : Set Real}
-- given
  (hU : IsOpen U)
  (hzero : 0 ∈ U)
  (hpositive : uIcc 0 h ⊆ U)
  (hnegative : uIcc 0 (-h) ⊆ U)
  (hg : ContDiffOn Real 4 g U)
  (hM : forall t, t ∈ U -> |iteratedDeriv 4 g t| <= M) :
-- imply
  CenteredFourthOrderSegmentData g h M where atZero := by
-- proof
  apply StatMech.Universality.CenteredFourthOrderSegmentData.ofContDiffOn hU hzero hpositive hnegative hg hM

/--
[centralSecondDifference_remainder_le_of_segmentData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalFourthOrder.lean)
-/
@[path]
private lemma centralSecondDifference_remainder_le_of_segmentData_eq
  {H : CenteredFourthOrderSegmentData g h M}
-- given
  (g : Real -> Real)
  (h M : Real) :
-- imply
  |(g h + g (-h) - 2 * g 0) - iteratedDeriv 2 g 0 * h ^ 2| <= M * |h| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.centralSecondDifference_remainder_le_of_segmentData g h M H

/--
[harmonicDirectionalFourNeighborStencil_le_of_segmentData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalFourthOrder.lean)
-/
@[path]
private lemma harmonicDirectionalFourNeighborStencil_le_of_segmentData_eq
  {HOne : CenteredFourthOrderSegmentData gOne h MOne}
  {HTwo : CenteredFourthOrderSegmentData gTwo h MTwo}
-- given
  (gOne gTwo : Real -> Real)
  (h MOne MTwo : Real)
  (hharmonic : iteratedDeriv 2 gOne 0 + iteratedDeriv 2 gTwo 0 = 0) :
-- imply
  |directionalFourNeighborStencil gOne gTwo h| <= (MOne + MTwo) * |h| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.harmonicDirectionalFourNeighborStencil_le_of_segmentData gOne gTwo h MOne MTwo HOne HTwo hharmonic

/--
[complexDirectionalFourNeighborStencil_le_of_segmentData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalFourthOrder.lean)
-/
@[path]
private lemma complexDirectionalFourNeighborStencil_le_of_segmentData_eq
  {z vOne vTwo : Complex}
-- given
  (f : Complex -> Real)
  (h MOne MTwo : Real)
  (HOne : CenteredFourthOrderSegmentData (fun t : Real => f (z + (t : Complex) * vOne)) h MOne)
  (HTwo : CenteredFourthOrderSegmentData (fun t : Real => f (z + (t : Complex) * vTwo)) h MTwo)
  (hharmonic : iteratedDeriv 2 (fun t : Real => f (z + (t : Complex) * vOne)) 0 + iteratedDeriv 2 (fun t : Real => f (z + (t : Complex) * vTwo)) 0 = 0) :
-- imply
  |complexDirectionalFourNeighborStencil f z vOne vTwo h| <= (MOne + MTwo) * |h| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.complexDirectionalFourNeighborStencil_le_of_segmentData f z vOne vTwo h MOne MTwo HOne HTwo hharmonic


-- created on 2026-10-23
