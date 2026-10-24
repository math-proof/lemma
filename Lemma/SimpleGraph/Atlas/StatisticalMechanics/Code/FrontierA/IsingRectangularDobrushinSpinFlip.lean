import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip
open Finset StatMech StatMech.Ising


/--
[rectangularPrismSpin_upperHalfFlip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushinSpinFlip.lean)
-/
@[path]
private lemma rectangularPrismSpin_upperHalfFlip_eq
  {m n h : Nat}
  {sigma : RectangularPrismConfig m n h}
  {x : Fin m}
  {y : Fin n}
  {z : Fin (2 * h + 1)} :
-- imply
  rectangularPrismSpin (rectangularPrismUpperHalfFlip sigma) x y z = if h < z.val then -rectangularPrismSpin sigma x y z else rectangularPrismSpin sigma x y z := by
-- proof
  apply StatMech.Ising.rectangularPrismSpin_upperHalfFlip sigma x y z

/--
[rectangularPrismDisorderSheet_not_mem_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushinSpinFlip.lean)
-/
@[path]
private lemma rectangularPrismDisorderSheet_not_mem_x_eq
  {m n h : Nat}
  {q : Fin (m - 1) × Fin n × Fin (2 * h + 1)} :
-- imply
  Sum.inl q ∉ rectangularPrismDisorderSheet m n h := by
-- proof
  apply StatMech.Ising.rectangularPrismDisorderSheet_not_mem_x q

/--
[rectangularPrismDisorderSheet_not_mem_y](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushinSpinFlip.lean)
-/
@[path]
private lemma rectangularPrismDisorderSheet_not_mem_y_eq
  {m n h : Nat}
  {q : Fin m × Fin (n - 1) × Fin (2 * h + 1)} :
-- imply
  Sum.inr (Sum.inl q) ∉ rectangularPrismDisorderSheet m n h := by
-- proof
  apply StatMech.Ising.rectangularPrismDisorderSheet_not_mem_y q

/--
[rectangularPrismDisorderSheet_mem_z_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushinSpinFlip.lean)
-/
@[path]
private lemma rectangularPrismDisorderSheet_mem_z_iff_eq
  {m n h : Nat}
  {q : Fin m × Fin n × Fin (2 * h)} :
-- imply
  Sum.inr (Sum.inr (Sum.inl q)) ∈ rectangularPrismDisorderSheet m n h <-> q.2.2.val = h := by
-- proof
  apply StatMech.Ising.rectangularPrismDisorderSheet_mem_z_iff q

/--
[rectangularPrismDisorderSheet_not_mem_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushinSpinFlip.lean)
-/
@[path]
private lemma rectangularPrismDisorderSheet_not_mem_boundary_eq
  {m n h : Nat}
  {v : RectangularPrismSite m n h} :
-- imply
  Sum.inr (Sum.inr (Sum.inr v)) ∉ rectangularPrismDisorderSheet m n h := by
-- proof
  apply StatMech.Ising.rectangularPrismDisorderSheet_not_mem_boundary v

/--
[reverseSheet_mul_monomial_upperHalfFlip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushinSpinFlip.lean)
-/
@[path]
private lemma reverseSheet_mul_monomial_upperHalfFlip_eq
  {J beta : Real}
  {m n h : Nat}
  {q : RectangularPrismInteraction m n h}
  {sigma : RectangularPrismConfig m n h} :
-- imply
  reverseInteractionCoupling (rectangularPrismInteractionCoupling J beta) (rectangularPrismDisorderSheet m n h) q * rectangularPrismInteractionMonomial q (rectangularPrismUpperHalfFlip sigma) = rectangularPrismDobrushinCoupling J beta q * rectangularPrismInteractionMonomial q sigma := by
-- proof
  apply StatMech.Ising.reverseSheet_mul_monomial_upperHalfFlip J beta q sigma

/--
[rectangularPrismTwistedPartition_eq_dobrushinPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushinSpinFlip.lean)
-/
@[path]
private lemma rectangularPrismTwistedPartition_eq_dobrushinPartition_eq
  {J beta : Real}
-- given
  (m n h : Nat) :
-- imply
  rectangularPrismTwistedPartition J beta m n h = rectangularPrismDobrushinPartition J beta m n h := by
-- proof
  apply StatMech.Ising.rectangularPrismTwistedPartition_eq_dobrushinPartition J beta m n h

/--
[rectangularDobrushinFreeEnergy_eq_boundaryRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushinSpinFlip.lean)
-/
@[path]
private lemma rectangularDobrushinFreeEnergy_eq_boundaryRatio_eq
  {J beta : Real}
-- given
  (m n h : Nat) :
-- imply
  rectangularDobrushinFreeEnergy J beta m n h = Real.log (rectangularPrismPlusPartition J beta m n h) - Real.log (rectangularPrismDobrushinPartition J beta m n h) := by
-- proof
  apply StatMech.Ising.rectangularDobrushinFreeEnergy_eq_boundaryRatio J beta m n h


-- created on 2026-10-23
