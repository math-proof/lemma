import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalEnergy
open StatMech StatMech.Universality


/--
[fkIsingSquareWiredIntegratedPrimitive_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalEnergy.lean)
-/
@[path]
private lemma fkIsingSquareWiredIntegratedPrimitive_nonneg_eq
  {n : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (horizontalCarrier verticalCarrier : Nat → Nat → FKIsingSquareWiredCarrier n) :
-- imply
  0 ≤ fkIsingSquareWiredIntegratedPrimitive n hn horizontalCarrier verticalCarrier i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredIntegratedPrimitive_nonneg n hn horizontalCarrier verticalCarrier i j

/--
[fkIsingSquareWiredIntegratedPrimitive_horizontal_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalEnergy.lean)
-/
@[path]
private lemma fkIsingSquareWiredIntegratedPrimitive_horizontal_increment_eq
  {n : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (horizontalCarrier verticalCarrier : Nat → Nat → FKIsingSquareWiredCarrier n)
  (hclosed : IsingRectangleClosedOneForm (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn (horizontalCarrier i j)) (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn (verticalCarrier i j))) :
-- imply
  fkIsingSquareWiredIntegratedPrimitive n hn horizontalCarrier verticalCarrier (i + 1) j - fkIsingSquareWiredIntegratedPrimitive n hn horizontalCarrier verticalCarrier i j = fkIsingSquareWiredPrimitiveIncrement n hn (horizontalCarrier i j) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredIntegratedPrimitive_horizontal_increment n hn horizontalCarrier verticalCarrier hclosed i j

/--
[fkIsingSquareWiredIntegratedPrimitive_vertical_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalEnergy.lean)
-/
@[path]
private lemma fkIsingSquareWiredIntegratedPrimitive_vertical_increment_eq
  {n : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (horizontalCarrier verticalCarrier : Nat → Nat → FKIsingSquareWiredCarrier n) :
-- imply
  fkIsingSquareWiredIntegratedPrimitive n hn horizontalCarrier verticalCarrier i (j + 1) - fkIsingSquareWiredIntegratedPrimitive n hn horizontalCarrier verticalCarrier i j = fkIsingSquareWiredPrimitiveIncrement n hn (verticalCarrier i j) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredIntegratedPrimitive_vertical_increment n hn horizontalCarrier verticalCarrier i j

/--
[fkIsingSquareWired_physicalNormalized_normSq_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalEnergy.lean)
-/
@[path]
private lemma fkIsingSquareWired_physicalNormalized_normSq_sum_le_eq
  {n : Nat}
  {C mesh L : Real}
-- given
  (hn : 0 < n)
  (horizontalCarrier verticalCarrier : Nat → Nat → FKIsingSquareWiredCarrier n)
  (hclosed : IsingRectangleClosedOneForm (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn (horizontalCarrier i j)) (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn (verticalCarrier i j)))
  (width height : Nat)
  (hupper : ∀ i j, fkIsingSquareWiredIntegratedPrimitive n hn horizontalCarrier verticalCarrier i j ≤ C)
  (hmesh : 0 < mesh)
  (hC : 0 ≤ C)
  (hscale : mesh * (height + width) ≤ L) :
-- imply
  mesh ^ 2 * ((∑ j ∈ range height, ∑ i ∈ range width, Complex.normSq (fkIsingSquareWiredObservableGrid n hn horizontalCarrier i j / (Real.sqrt (2 * mesh) : Complex))) + (∑ i ∈ range width, ∑ j ∈ range height, Complex.normSq (fkIsingSquareWiredObservableGrid n hn verticalCarrier i j / (Real.sqrt (2 * mesh) : Complex)))) ≤ L * C / 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_physicalNormalized_normSq_sum_le n hn horizontalCarrier verticalCarrier hclosed C mesh L width height hupper hmesh hC hscale


-- created on 2026-10-23
