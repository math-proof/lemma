import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointPointwise
open StatMech StatMech.Universality


/--
[isingLeapfrogStoppedKernel_twoApartX_horizontalEndpoint_diffusive_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointPointwise.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_twoApartX_horizontalEndpoint_diffusive_abs_le_eq
  {R level rho : Nat}
  {west east q : IsingLeapfrogBox R}
-- given
  (hwest : west.1.1 + 1 = level)
  (heast : east.1.1 = level + 1)
  (hy : west.2.1 = east.2.1)
  (hρ : 0 < rho)
  (hleft : rho <= level)
  (hright : level + rho <= R)
  (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
-- imply
  |isingLeapfrogStoppedKernel R (rho * rho) west q - isingLeapfrogStoppedKernel R (rho * rho) east q| <= 3276 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_twoApartX_horizontalEndpoint_diffusive_abs_le R level rho west east q hwest heast hy hρ hleft hright hqHorizontal

/--
[isingLeapfrogStoppedKernel_twoApartX_boundary_diffusive_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointPointwise.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_twoApartX_boundary_diffusive_abs_le_eq
  {R level rho : Nat}
  {west east q : IsingLeapfrogBox R}
-- given
  (hwest : west.1.1 + 1 = level)
  (heast : east.1.1 = level + 1)
  (hy : west.2.1 = east.2.1)
  (hρ : 0 < rho)
  (hleft : rho <= level)
  (hright : level + rho <= R)
  (hbottom : rho <= west.2.1)
  (htop : west.2.1 + rho <= R)
  (hqBoundary : isingLeapfrogBoxBoundary R q) :
-- imply
  |isingLeapfrogStoppedKernel R (rho * rho) west q - isingLeapfrogStoppedKernel R (rho * rho) east q| <= 10296 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_twoApartX_boundary_diffusive_abs_le R level rho west east q hwest heast hy hρ hleft hright hbottom htop hqBoundary

/--
[isingLeapfrogStoppedKernel_twoApartY_verticalEndpoint_diffusive_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointPointwise.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_twoApartY_verticalEndpoint_diffusive_abs_le_eq
  {R level rho : Nat}
  {south north q : IsingLeapfrogBox R}
-- given
  (hsouth : south.2.1 + 1 = level)
  (hnorth : north.2.1 = level + 1)
  (hx : south.1.1 = north.1.1)
  (hρ : 0 < rho)
  (hbottom : rho <= level)
  (htop : level + rho <= R)
  (hqVertical : q.2.1 = 0 ∨ q.2.1 = R) :
-- imply
  |isingLeapfrogStoppedKernel R (rho * rho) south q - isingLeapfrogStoppedKernel R (rho * rho) north q| <= 3276 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_twoApartY_verticalEndpoint_diffusive_abs_le R level rho south north q hsouth hnorth hx hρ hbottom htop hqVertical

/--
[isingLeapfrogStoppedKernel_twoApartY_boundary_diffusive_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointPointwise.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_twoApartY_boundary_diffusive_abs_le_eq
  {R level rho : Nat}
  {south north q : IsingLeapfrogBox R}
-- given
  (hsouth : south.2.1 + 1 = level)
  (hnorth : north.2.1 = level + 1)
  (hx : south.1.1 = north.1.1)
  (hρ : 0 < rho)
  (hbottom : rho <= level)
  (htop : level + rho <= R)
  (hleft : rho <= south.1.1)
  (hright : south.1.1 + rho <= R)
  (hqBoundary : isingLeapfrogBoxBoundary R q) :
-- imply
  |isingLeapfrogStoppedKernel R (rho * rho) south q - isingLeapfrogStoppedKernel R (rho * rho) north q| <= 10296 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_twoApartY_boundary_diffusive_abs_le R level rho south north q hsouth hnorth hx hρ hbottom htop hleft hright hqBoundary

/--
[isingLeapfrogExitKernel_neighbor_timeOffset_boundary_diffusive_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointPointwise.lean)
-/
@[path]
private lemma isingLeapfrogExitKernel_neighbor_timeOffset_boundary_diffusive_abs_le_eq
  {R rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hρ : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p')
  (hq : isingLeapfrogBoxBoundary R q) :
-- imply
  |isingLeapfrogExitKernel R (rho * rho) p q - isingLeapfrogExitKernel R (rho * rho + 1) p' q| <= 6786 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernel_neighbor_timeOffset_boundary_diffusive_abs_le R rho p p' q hρ hp hp' hpp' hq

/--
[isingLeapfrogExitKernel_neighbor_timeOffset_diffusive_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointPointwise.lean)
-/
@[path]
private lemma isingLeapfrogExitKernel_neighbor_timeOffset_diffusive_abs_le_eq
  {R rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hρ : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  |isingLeapfrogExitKernel R (rho * rho) p q - isingLeapfrogExitKernel R (rho * rho + 1) p' q| <= 6786 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernel_neighbor_timeOffset_diffusive_abs_le R rho p p' q hρ hp hp' hpp'

/--
[isingLeapfrogDiffusiveExitInputs_fermionic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointPointwise.lean)
-/
@[path]
private lemma isingLeapfrogDiffusiveExitInputs_fermionic_eq :
-- imply
  IsingLeapfrogDiffusiveExitInputs 6786 152 := by
-- proof
  apply StatMech.Universality.isingLeapfrogDiffusiveExitInputs_fermionic

/--
[isingLeapfrogDiffusiveGradientBound_fermionic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointPointwise.lean)
-/
@[path]
private lemma isingLeapfrogDiffusiveGradientBound_fermionic_eq :
-- imply
  IsingLeapfrogDiffusiveGradientBound 1032080 := by
-- proof
  apply StatMech.Universality.isingLeapfrogDiffusiveGradientBound_fermionic

/--
[fkIsingSquareRadialPatchFullObservableWindow_normSq_sub_le_diffusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointPointwise.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchFullObservableWindow_normSq_sub_le_diffusive_eq
  {n m baseI baseJ R rho : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hm : m <= n)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hρ : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  Complex.normSq (fkIsingSquareRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p - fkIsingSquareRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p') <= (1032080 / (rho : Real) ^ 3) * ∑ q, Complex.normSq (fkIsingSquareRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ q) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchFullObservableWindow_normSq_sub_le_diffusive n m baseI baseJ R rho hn hm hfitI hfitJ p p' hρ hp hp' hpp'

/--
[fkIsingSquareRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le_diffusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointPointwise.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le_diffusive_eq
  {n m baseI baseJ R rho : Nat}
  {mesh : Real}
  {p p' : IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hm : m <= n)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hmesh : 0 < mesh)
  (hρ : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  Complex.normSq (fkIsingSquareRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p / (Real.sqrt (2 * mesh) : Complex) - fkIsingSquareRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p' / (Real.sqrt (2 * mesh) : Complex)) <= (1032080 / (rho : Real) ^ 3) * ∑ q, Complex.normSq (fkIsingSquareRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ q / (Real.sqrt (2 * mesh) : Complex)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le_diffusive n m baseI baseJ R rho mesh hn hm hfitI hfitJ hmesh p p' hρ hp hp' hpp'


-- created on 2026-10-23
