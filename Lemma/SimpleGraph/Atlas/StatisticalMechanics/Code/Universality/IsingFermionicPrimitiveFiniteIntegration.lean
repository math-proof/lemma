import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveFiniteIntegration
open StatMech StatMech.Universality


/--
[isingRectangle_vertical_sum_column_difference_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveFiniteIntegration.lean)
-/
@[path]
private lemma isingRectangle_vertical_sum_column_difference_on_eq
  {i j : Nat}
-- given
  (horizontal vertical : Nat → Nat → Real)
  (width height : Nat)
  (hclosed : IsingRectangleClosedOneFormOn horizontal vertical width height)
  (hi : i < width)
  (hj : j ≤ height) :
-- imply
  (∑ l ∈ range j, vertical (i + 1) l) - ∑ l ∈ range j, vertical i l = horizontal i j - horizontal i 0 := by
-- proof
  apply StatMech.Universality.isingRectangle_vertical_sum_column_difference_on horizontal vertical width height hclosed i j hi hj

/--
[isingRectanglePrimitive_horizontal_increment_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveFiniteIntegration.lean)
-/
@[path]
private lemma isingRectanglePrimitive_horizontal_increment_on_eq
  {i j : Nat}
-- given
  (horizontal vertical : Nat → Nat → Real)
  (width height : Nat)
  (hclosed : IsingRectangleClosedOneFormOn horizontal vertical width height)
  (hi : i < width)
  (hj : j ≤ height) :
-- imply
  isingRectanglePrimitive horizontal vertical (i + 1) j - isingRectanglePrimitive horizontal vertical i j = horizontal i j := by
-- proof
  apply StatMech.Universality.isingRectanglePrimitive_horizontal_increment_on horizontal vertical width height hclosed i j hi hj

/--
[isingRectangle_horizontal_sum_eq_primitive_difference_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveFiniteIntegration.lean)
-/
@[path]
private lemma isingRectangle_horizontal_sum_eq_primitive_difference_on_eq
-- given
  (horizontal vertical : Nat → Nat → Real)
  (width height j : Nat)
  (hclosed : IsingRectangleClosedOneFormOn horizontal vertical width height)
  (hj : j ≤ height) :
-- imply
  (∑ i ∈ range width, horizontal i j) = isingRectanglePrimitive horizontal vertical width j - isingRectanglePrimitive horizontal vertical 0 j := by
-- proof
  apply StatMech.Universality.isingRectangle_horizontal_sum_eq_primitive_difference_on horizontal vertical width height j hclosed hj

/--
[isingRectangle_increment_sum_le_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveFiniteIntegration.lean)
-/
@[path]
private lemma isingRectangle_increment_sum_le_on_eq
  {C : Real}
-- given
  (horizontal vertical : Nat → Nat → Real)
  (width height : Nat)
  (hclosed : IsingRectangleClosedOneFormOn horizontal vertical width height)
  (hlower : ∀ i ≤ width, ∀ j ≤ height, 0 ≤ isingRectanglePrimitive horizontal vertical i j)
  (hupper : ∀ i ≤ width, ∀ j ≤ height, isingRectanglePrimitive horizontal vertical i j ≤ C) :
-- imply
  (∑ j ∈ range height, ∑ i ∈ range width, horizontal i j) + (∑ i ∈ range width, ∑ j ∈ range height, vertical i j) ≤ (height + width) * C := by
-- proof
  apply StatMech.Universality.isingRectangle_increment_sum_le_on horizontal vertical C width height hclosed hlower hupper

/--
[isingRectangle_scaled_increment_sum_le_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveFiniteIntegration.lean)
-/
@[path]
private lemma isingRectangle_scaled_increment_sum_le_on_eq
  {C mesh L : Real}
-- given
  (horizontal vertical : Nat → Nat → Real)
  (width height : Nat)
  (hclosed : IsingRectangleClosedOneFormOn horizontal vertical width height)
  (hlower : ∀ i ≤ width, ∀ j ≤ height, 0 ≤ isingRectanglePrimitive horizontal vertical i j)
  (hupper : ∀ i ≤ width, ∀ j ≤ height, isingRectanglePrimitive horizontal vertical i j ≤ C)
  (hmesh : 0 ≤ mesh)
  (hC : 0 ≤ C)
  (hscale : mesh * (height + width) ≤ L) :
-- imply
  mesh * ((∑ j ∈ range height, ∑ i ∈ range width, horizontal i j) + (∑ i ∈ range width, ∑ j ∈ range height, vertical i j)) ≤ L * C := by
-- proof
  apply StatMech.Universality.isingRectangle_scaled_increment_sum_le_on horizontal vertical C mesh L width height hclosed hlower hupper hmesh hC hscale

/--
[isingRectangle_physicalNormalized_normSq_sum_le_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveFiniteIntegration.lean)
-/
@[path]
private lemma isingRectangle_physicalNormalized_normSq_sum_le_on_eq
  {C mesh L : Real}
-- given
  (horizontalF verticalF : Nat → Nat → Complex)
  (width height : Nat)
  (hclosed : IsingRectangleClosedOneFormOn (fun i j ↦ isingPrimitiveIncrement (horizontalF i j)) (fun i j ↦ isingPrimitiveIncrement (verticalF i j)) width height)
  (hlower : ∀ i ≤ width, ∀ j ≤ height, 0 ≤ isingRectanglePrimitive (fun a b ↦ isingPrimitiveIncrement (horizontalF a b)) (fun a b ↦ isingPrimitiveIncrement (verticalF a b)) i j)
  (hupper : ∀ i ≤ width, ∀ j ≤ height, isingRectanglePrimitive (fun a b ↦ isingPrimitiveIncrement (horizontalF a b)) (fun a b ↦ isingPrimitiveIncrement (verticalF a b)) i j ≤ C)
  (hmesh : 0 < mesh)
  (hC : 0 ≤ C)
  (hscale : mesh * (height + width) ≤ L) :
-- imply
  mesh ^ 2 * ((∑ j ∈ range height, ∑ i ∈ range width, Complex.normSq (horizontalF i j / (Real.sqrt (2 * mesh) : Complex))) + (∑ i ∈ range width, ∑ j ∈ range height, Complex.normSq (verticalF i j / (Real.sqrt (2 * mesh) : Complex)))) ≤ L * C / 2 := by
-- proof
  apply StatMech.Universality.isingRectangle_physicalNormalized_normSq_sum_le_on horizontalF verticalF C mesh L width height hclosed hlower hupper hmesh hC hscale


-- created on 2026-10-23
