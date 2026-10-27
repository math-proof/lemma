import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushin
open Finset StatMech StatMech.Ising


/--
[rectangularPrismInteractionMonomial_isSpinMonomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean)
-/
@[path]
private lemma rectangularPrismInteractionMonomial_isSpinMonomial_eq
  {m n h : Nat}
  {q : RectangularPrismInteraction m n h} :
-- imply
  IsSpinMonomial (rectangularPrismInteractionMonomial q) := by
-- proof
  apply StatMech.Ising.rectangularPrismInteractionMonomial_isSpinMonomial q

/--
[rectangularPrismInteractionMonomial_eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean)
-/
@[path]
private lemma rectangularPrismInteractionMonomial_eq_one_or_neg_one_eq
  {m n h : Nat}
  {q : RectangularPrismInteraction m n h}
  {sigma : RectangularPrismConfig m n h} :
-- imply
  rectangularPrismInteractionMonomial q sigma = 1 ∨ rectangularPrismInteractionMonomial q sigma = -1 := by
-- proof
  apply StatMech.Ising.rectangularPrismInteractionMonomial_eq_one_or_neg_one q sigma

/--
[rectangularPrismInteractionCoupling_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean)
-/
@[path]
private lemma rectangularPrismInteractionCoupling_nonneg_eq
  {J beta : Real}
  {m n h : Nat}
  {q : RectangularPrismInteraction m n h}
-- given
  (hJ : 0 <= J)
  (hbeta : 0 <= beta) :
-- imply
  0 <= rectangularPrismInteractionCoupling J beta q := by
-- proof
  apply StatMech.Ising.rectangularPrismInteractionCoupling_nonneg hJ hbeta q

/--
[sum_rectangularPrismInteraction_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean)
-/
@[path]
private lemma sum_rectangularPrismInteraction_eq_eq
  {J beta : Real}
  {m n h : Nat}
  {sigma : RectangularPrismConfig m n h} :
-- imply
  (∑ q : RectangularPrismInteraction m n h, rectangularPrismInteractionCoupling J beta q * rectangularPrismInteractionMonomial q sigma) = beta * J * (rectangularPrismInternalInteraction sigma + rectangularPrismPlusBoundaryInteraction sigma) := by
-- proof
  apply StatMech.Ising.sum_rectangularPrismInteraction_eq J beta sigma

/--
[sum_rectangularPrismDisorderSheet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean)
-/
@[path]
private lemma sum_rectangularPrismDisorderSheet_eq_eq
  {J beta : Real}
  {m n h : Nat}
  {sigma : RectangularPrismConfig m n h} :
-- imply
  (∑ q ∈ rectangularPrismDisorderSheet m n h, rectangularPrismInteractionCoupling J beta q * rectangularPrismInteractionMonomial q sigma) = beta * J * rectangularPrismInterfaceInteraction sigma := by
-- proof
  apply StatMech.Ising.sum_rectangularPrismDisorderSheet_eq J beta sigma

/--
[rectangularPrismPlusPartition_eq_monomialInteractionPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean)
-/
@[path]
private lemma rectangularPrismPlusPartition_eq_monomialInteractionPartition_eq
  {J beta : Real}
-- given
  (m n h : Nat) :
-- imply
  rectangularPrismPlusPartition J beta m n h = monomialInteractionPartition (rectangularPrismInteractionCoupling J beta : RectangularPrismInteraction m n h -> Real) (rectangularPrismInteractionMonomial : RectangularPrismInteraction m n h -> RectangularPrismConfig m n h -> Real) := by
-- proof
  apply StatMech.Ising.rectangularPrismPlusPartition_eq_monomialInteractionPartition J beta m n h

/--
[rectangularPrismTwistedPartition_eq_monomialInteractionPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean)
-/
@[path]
private lemma rectangularPrismTwistedPartition_eq_monomialInteractionPartition_eq
  {J beta : Real}
-- given
  (m n h : Nat) :
-- imply
  rectangularPrismTwistedPartition J beta m n h = monomialInteractionPartition (reverseInteractionCoupling (rectangularPrismInteractionCoupling J beta : RectangularPrismInteraction m n h -> Real) (rectangularPrismDisorderSheet m n h)) (rectangularPrismInteractionMonomial : RectangularPrismInteraction m n h -> RectangularPrismConfig m n h -> Real) := by
-- proof
  apply StatMech.Ising.rectangularPrismTwistedPartition_eq_monomialInteractionPartition J beta m n h

/--
[rectangularPrismTwistedPartition_le_plusPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean)
-/
@[path]
private lemma rectangularPrismTwistedPartition_le_plusPartition_eq
  {J beta : Real}
-- given
  (hJ : 0 <= J)
  (hbeta : 0 <= beta)
  (m n h : Nat) :
-- imply
  rectangularPrismTwistedPartition J beta m n h <= rectangularPrismPlusPartition J beta m n h := by
-- proof
  apply StatMech.Ising.rectangularPrismTwistedPartition_le_plusPartition hJ hbeta m n h

/--
[rectangularDobrushinFreeEnergy_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean)
-/
@[path]
private lemma rectangularDobrushinFreeEnergy_nonneg_eq
  {J beta : Real}
-- given
  (hJ : 0 <= J)
  (hbeta : 0 <= beta)
  (m n h : Nat) :
-- imply
  0 <= rectangularDobrushinFreeEnergy J beta m n h := by
-- proof
  apply StatMech.Ising.rectangularDobrushinFreeEnergy_nonneg hJ hbeta m n h

/--
[rectangularDobrushinArray_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean)
-/
@[path]
private lemma rectangularDobrushinArray_nonneg_eq
  {J beta : Real}
  {m n : Nat}
-- given
  (hJ : 0 <= J)
  (hbeta : 0 <= beta) :
-- imply
  0 <= rectangularDobrushinArray J beta m n := by
-- proof
  apply StatMech.Ising.rectangularDobrushinArray_nonneg hJ hbeta m n

/--
[rectangularPrismInterfaceSummand_abs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean)
-/
@[path]
private lemma rectangularPrismInterfaceSummand_abs_le_one_eq
  {m n h : Nat}
  {sigma : RectangularPrismConfig m n h}
  {x : Fin m}
  {y : Fin n}
-- given
  (hh : 0 < h) :
-- imply
  |rectangularPrismSpin sigma x y ⟨h, by omega⟩ * rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩| <= 1 := by
-- proof
  apply StatMech.Ising.rectangularPrismInterfaceSummand_abs_le_one sigma hh x y

/--
[rectangularPrismInterfaceInteraction_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean)
-/
@[path]
private lemma rectangularPrismInterfaceInteraction_abs_le_eq
  {m n h : Nat}
  {sigma : RectangularPrismConfig m n h} :
-- imply
  |rectangularPrismInterfaceInteraction sigma| <= (m : Real) * n := by
-- proof
  apply StatMech.Ising.rectangularPrismInterfaceInteraction_abs_le sigma

/--
[rectangularPrism_energy_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean)
-/
@[path]
private lemma rectangularPrism_energy_sub_abs_le_eq
  {J : Real}
  {m n h : Nat}
  {sigma : RectangularPrismConfig m n h} :
-- imply
  |rectangularPrismPlusEnergy J sigma - rectangularPrismTwistedEnergy J sigma| <= 2 * |J| * ((m : Real) * n) := by
-- proof
  apply StatMech.Ising.rectangularPrism_energy_sub_abs_le J sigma

/--
[rectangularDobrushinFreeEnergy_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean)
-/
@[path]
private lemma rectangularDobrushinFreeEnergy_abs_le_eq
  {J beta : Real}
-- given
  (m n h : Nat) :
-- imply
  |rectangularDobrushinFreeEnergy J beta m n h| <= 2 * |beta| * |J| * ((m : Real) * n) := by
-- proof
  apply StatMech.Ising.rectangularDobrushinFreeEnergy_abs_le J beta m n h

/--
[rectangularDobrushinArray_le_area](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean)
-/
@[path]
private lemma rectangularDobrushinArray_le_area_eq
  {J beta : Real}
  {m n : Nat} :
-- imply
  rectangularDobrushinArray J beta m n <= (2 * |beta| * |J|) * (m : Real) * n := by
-- proof
  apply StatMech.Ising.rectangularDobrushinArray_le_area J beta m n


-- created on 2026-10-23
