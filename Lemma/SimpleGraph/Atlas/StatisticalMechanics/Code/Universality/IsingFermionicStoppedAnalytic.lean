import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicStoppedAnalytic
open StatMech StatMech.Universality


/--
[isingLeapfrogBoxSwap_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean)
-/
@[path]
private lemma isingLeapfrogBoxSwap_involutive_eq
  {R : Nat}
  {p : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogBoxSwap R (isingLeapfrogBoxSwap R p) = p := by
-- proof
  apply StatMech.Universality.isingLeapfrogBoxSwap_involutive R p

/--
[isingLeapfrogBoxSwap_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean)
-/
@[path]
private lemma isingLeapfrogBoxSwap_eq_iff_eq
  {R : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogBoxSwap R p = isingLeapfrogBoxSwap R q ↔ p = q := by
-- proof
  apply StatMech.Universality.isingLeapfrogBoxSwap_eq_iff R p q

/--
[isingLeapfrogBoxBoundary_swap_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean)
-/
@[path]
private lemma isingLeapfrogBoxBoundary_swap_iff_eq
  {R : Nat}
  {p : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogBoxBoundary R (isingLeapfrogBoxSwap R p) ↔ isingLeapfrogBoxBoundary R p := by
-- proof
  apply StatMech.Universality.isingLeapfrogBoxBoundary_swap_iff R p

/--
[isingLeapfrogStoppedKernel_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_swap_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedKernel R t (isingLeapfrogBoxSwap R p) (isingLeapfrogBoxSwap R q) = isingLeapfrogStoppedKernel R t p q := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_swap R t p q

/--
[isingLeapfrogBoxInt_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean)
-/
@[path]
private lemma isingLeapfrogBoxInt_swap_eq
  {R : Nat}
  {p : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogBoxInt (isingLeapfrogBoxSwap R p) = ((isingLeapfrogBoxInt p).2, (isingLeapfrogBoxInt p).1) := by
-- proof
  apply StatMech.Universality.isingLeapfrogBoxInt_swap R p

/--
[isingLeapfrogStoppedKernel_reflectedStartY_diffusive_l1_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_reflectedStartY_diffusive_l1_le_eq
  {R level rho : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).2 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = ((isingLeapfrogBoxInt p).1, 2 * (level : Int) - (isingLeapfrogBoxInt p).2))
  (hρ : 0 < rho)
  (hbottom : rho ≤ level)
  (htop : level + rho ≤ R)
  (hleft : rho ≤ p.1.1)
  (hright : p.1.1 + rho ≤ R) :
-- imply
  (∑ q : IsingLeapfrogBox R, |isingLeapfrogStoppedKernel R (rho * rho) p q - isingLeapfrogStoppedKernel R (rho * rho) p' q|) ≤ 76 / (rho : Real) := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_reflectedStartY_diffusive_l1_le R level rho p p' hstart hmirror hρ hbottom htop hleft hright

/--
[isingLeapfrogStoppedKernel_l1_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_l1_le_two_eq
  {R t t' : Nat}
  {p p' : IsingLeapfrogBox R} :
-- imply
  (∑ q, |isingLeapfrogStoppedKernel R t p q - isingLeapfrogStoppedKernel R t' p' q|) ≤ 2 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_l1_le_two R t t' p p'

/--
[isingLeapfrogStoppedKernel_l1_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_l1_triangle_eq
  {R t : Nat}
  {p p' p'' : IsingLeapfrogBox R} :
-- imply
  (∑ q, |isingLeapfrogStoppedKernel R t p q - isingLeapfrogStoppedKernel R t p'' q|) ≤ (∑ q, |isingLeapfrogStoppedKernel R t p q - isingLeapfrogStoppedKernel R t p' q|) + ∑ q, := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_l1_triangle R t p p' p''

/--
[isingLeapfrogStoppedKernel_twoApartX_diffusive_l1_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_twoApartX_diffusive_l1_le_eq
  {R level rho : Nat}
  {west east : IsingLeapfrogBox R}
-- given
  (hwest : west.1.1 + 1 = level)
  (heast : east.1.1 = level + 1)
  (hy : west.2.1 = east.2.1)
  (hρ : 0 < rho)
  (hleft : rho ≤ level)
  (hright : level + rho ≤ R)
  (hbottom : rho ≤ west.2.1)
  (htop : west.2.1 + rho ≤ R) :
-- imply
  (∑ q, |isingLeapfrogStoppedKernel R (rho * rho) west q - isingLeapfrogStoppedKernel R (rho * rho) east q|) ≤ 76 / (rho : Real) := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_twoApartX_diffusive_l1_le R level rho west east hwest heast hy hρ hleft hright hbottom htop

/--
[isingLeapfrogStoppedKernel_twoApartY_diffusive_l1_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_twoApartY_diffusive_l1_le_eq
  {R level rho : Nat}
  {south north : IsingLeapfrogBox R}
-- given
  (hsouth : south.2.1 + 1 = level)
  (hnorth : north.2.1 = level + 1)
  (hx : south.1.1 = north.1.1)
  (hρ : 0 < rho)
  (hbottom : rho ≤ level)
  (htop : level + rho ≤ R)
  (hleft : rho ≤ south.1.1)
  (hright : south.1.1 + rho ≤ R) :
-- imply
  (∑ q, |isingLeapfrogStoppedKernel R (rho * rho) south q - isingLeapfrogStoppedKernel R (rho * rho) north q|) ≤ 76 / (rho : Real) := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_twoApartY_diffusive_l1_le R level rho south north hsouth hnorth hx hρ hbottom htop hleft hright

/--
[isingLeapfrogStoppedKernel_twoApartX_later_l1_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_twoApartX_later_l1_le_eq
  {R t level radius : Nat}
  {west east : IsingLeapfrogBox R}
-- given
  (ht : radius * radius ≤ t)
  (hwest : west.1.1 + 1 = level)
  (heast : east.1.1 = level + 1)
  (hy : west.2.1 = east.2.1)
  (hradius : 0 < radius)
  (hleft : radius ≤ level)
  (hright : level + radius ≤ R)
  (hbottom : radius ≤ west.2.1)
  (htop : west.2.1 + radius ≤ R) :
-- imply
  (∑ q, |isingLeapfrogStoppedKernel R t west q - isingLeapfrogStoppedKernel R t east q|) ≤ 76 / (radius : Real) := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_twoApartX_later_l1_le R t level radius west east ht hwest heast hy hradius hleft hright hbottom htop

/--
[isingLeapfrogStoppedKernel_twoApartY_later_l1_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_twoApartY_later_l1_le_eq
  {R t level radius : Nat}
  {south north : IsingLeapfrogBox R}
-- given
  (ht : radius * radius ≤ t)
  (hsouth : south.2.1 + 1 = level)
  (hnorth : north.2.1 = level + 1)
  (hx : south.1.1 = north.1.1)
  (hradius : 0 < radius)
  (hbottom : radius ≤ level)
  (htop : level + radius ≤ R)
  (hleft : radius ≤ south.1.1)
  (hright : south.1.1 + radius ≤ R) :
-- imply
  (∑ q, |isingLeapfrogStoppedKernel R t south q - isingLeapfrogStoppedKernel R t north q|) ≤ 76 / (radius : Real) := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_twoApartY_later_l1_le R t level radius south north ht hsouth hnorth hx hradius hbottom htop hleft hright

/--
[isingLeapfrogStoppedKernel_neighbor_timeOffset_l1_le_of_predecessors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_neighbor_timeOffset_l1_le_of_predecessors_eq
  {R t : Nat}
  {p p' : IsingLeapfrogBox R}
  {C : Real}
-- given
  (hp' : ¬ isingLeapfrogBoxBoundary R p')
  (hpred : (∑ q, |isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p') q - isingLeapfrogStoppedKernel R t p q|) + (∑ q, |isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p' hp') q - isingLeapfrogStoppedKernel R t p q|) + (∑ q, |isingLeapfrogStoppedKernel R t (isingLeapfrogNW R p' hp') q - isingLeapfrogStoppedKernel R t p q|) + (∑ q, |isingLeapfrogStoppedKernel R t (isingLeapfrogNE R p' hp') q - isingLeapfrogStoppedKernel R t p q|) ≤ C) :
-- imply
  (∑ q, |isingLeapfrogStoppedKernel R t p q - isingLeapfrogStoppedKernel R (t + 1) p' q|) ≤ C / 4 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_neighbor_timeOffset_l1_le_of_predecessors R t p p' hp' C hpred

/--
[isingLeapfrogStoppedKernel_neighbor_timeOffset_diffusive_l1_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_neighbor_timeOffset_diffusive_l1_le_eq
  {R rho : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hρ : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  (∑ q, |isingLeapfrogStoppedKernel R (rho * rho) p q - isingLeapfrogStoppedKernel R (rho * rho + 1) p' q|) ≤ 152 / (rho : Real) := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_neighbor_timeOffset_diffusive_l1_le R rho p p' hρ hp hp' hpp'


-- created on 2026-10-23
