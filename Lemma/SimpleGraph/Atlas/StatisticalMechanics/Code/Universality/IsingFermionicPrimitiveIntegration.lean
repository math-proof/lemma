import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveIntegration
open Finset StatMech StatMech.Universality


/--
[isingRectanglePrimitiveWithBase_bottom_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectanglePrimitiveWithBase_bottom_boundary_eq
  {base : Real}
  {i : Nat}
-- given
  (horizontal vertical : Nat -> Nat -> Real) :
-- imply
  isingRectanglePrimitiveWithBase base horizontal vertical i 0 = base + ∑ k ∈ range i, horizontal k 0 := by
-- proof
  apply StatMech.Universality.isingRectanglePrimitiveWithBase_bottom_boundary base horizontal vertical i

/--
[isingRectanglePrimitiveWithBase_left_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectanglePrimitiveWithBase_left_boundary_eq
  {base : Real}
  {j : Nat}
-- given
  (horizontal vertical : Nat -> Nat -> Real) :
-- imply
  isingRectanglePrimitiveWithBase base horizontal vertical 0 j = base + ∑ l ∈ range j, vertical 0 l := by
-- proof
  apply StatMech.Universality.isingRectanglePrimitiveWithBase_left_boundary base horizontal vertical j

/--
[isingRectanglePrimitiveWithBase_axis_boundary_values](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectanglePrimitiveWithBase_axis_boundary_values_eq
  {base : Real}
-- given
  (horizontal vertical : Nat -> Nat -> Real)
  (hbottom : ∀ i, horizontal i 0 = 0)
  (hleft : ∀ j, vertical 0 j = 0) :
-- imply
  (∀ i, isingRectanglePrimitiveWithBase base horizontal vertical i 0 = base) ∧ (∀ j, isingRectanglePrimitiveWithBase base horizontal vertical 0 j = base) := by
-- proof
  apply StatMech.Universality.isingRectanglePrimitiveWithBase_axis_boundary_values base horizontal vertical hbottom hleft

/--
[isingRectanglePrimitive_vertical_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectanglePrimitive_vertical_increment_eq
  {i j : Nat}
-- given
  (horizontal vertical : Nat -> Nat -> Real) :
-- imply
  isingRectanglePrimitive horizontal vertical i (j + 1) - isingRectanglePrimitive horizontal vertical i j = vertical i j := by
-- proof
  apply StatMech.Universality.isingRectanglePrimitive_vertical_increment horizontal vertical i j

/--
[isingRectangle_vertical_sum_column_difference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectangle_vertical_sum_column_difference_eq
  {i j : Nat}
-- given
  (horizontal vertical : Nat -> Nat -> Real)
  (hclosed : IsingRectangleClosedOneForm horizontal vertical) :
-- imply
  (∑ l ∈ range j, vertical (i + 1) l) - ∑ l ∈ range j, vertical i l = horizontal i j - horizontal i 0 := by
-- proof
  apply StatMech.Universality.isingRectangle_vertical_sum_column_difference horizontal vertical hclosed i j

/--
[isingRectanglePrimitive_horizontal_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectanglePrimitive_horizontal_increment_eq
  {i j : Nat}
-- given
  (horizontal vertical : Nat -> Nat -> Real)
  (hclosed : IsingRectangleClosedOneForm horizontal vertical) :
-- imply
  isingRectanglePrimitive horizontal vertical (i + 1) j - isingRectanglePrimitive horizontal vertical i j = horizontal i j := by
-- proof
  apply StatMech.Universality.isingRectanglePrimitive_horizontal_increment horizontal vertical hclosed i j

/--
[isingRectanglePrimitive_eq_left_then_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectanglePrimitive_eq_left_then_top_eq
  {i j : Nat}
-- given
  (horizontal vertical : Nat -> Nat -> Real)
  (hclosed : IsingRectangleClosedOneForm horizontal vertical) :
-- imply
  isingRectanglePrimitive horizontal vertical i j = (∑ l ∈ range j, vertical 0 l) + ∑ k ∈ range i, horizontal k j := by
-- proof
  apply StatMech.Universality.isingRectanglePrimitive_eq_left_then_top horizontal vertical hclosed i j

/--
[isingRectangle_horizontal_sum_eq_primitive_difference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectangle_horizontal_sum_eq_primitive_difference_eq
  {width j : Nat}
-- given
  (horizontal vertical : Nat -> Nat -> Real)
  (hclosed : IsingRectangleClosedOneForm horizontal vertical) :
-- imply
  (∑ i ∈ range width, horizontal i j) = isingRectanglePrimitive horizontal vertical width j - isingRectanglePrimitive horizontal vertical 0 j := by
-- proof
  apply StatMech.Universality.isingRectangle_horizontal_sum_eq_primitive_difference horizontal vertical hclosed width j

/--
[isingRectangle_vertical_sum_eq_primitive_difference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectangle_vertical_sum_eq_primitive_difference_eq
-- given
  (horizontal vertical : Nat -> Nat -> Real)
  (i height : Nat) :
-- imply
  (∑ j ∈ range height, vertical i j) = isingRectanglePrimitive horizontal vertical i height - isingRectanglePrimitive horizontal vertical i 0 := by
-- proof
  apply StatMech.Universality.isingRectangle_vertical_sum_eq_primitive_difference horizontal vertical i height

/--
[isingPrimitiveIncrement_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingPrimitiveIncrement_nonneg_eq
  {F : Complex} :
-- imply
  0 <= isingPrimitiveIncrement F := by
-- proof
  apply StatMech.Universality.isingPrimitiveIncrement_nonneg F

/--
[isingRectanglePrimitive_horizontal_mono_of_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectanglePrimitive_horizontal_mono_of_increment_eq
  {i j : Nat}
-- given
  (horizontal vertical : Nat -> Nat -> Real)
  (hclosed : IsingRectangleClosedOneForm horizontal vertical)
  (hnonneg : forall i j, 0 <= horizontal i j) :
-- imply
  isingRectanglePrimitive horizontal vertical i j <= isingRectanglePrimitive horizontal vertical (i + 1) j := by
-- proof
  apply StatMech.Universality.isingRectanglePrimitive_horizontal_mono_of_increment horizontal vertical hclosed hnonneg i j

/--
[isingRectanglePrimitive_vertical_mono_of_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectanglePrimitive_vertical_mono_of_increment_eq
  {i j : Nat}
-- given
  (horizontal vertical : Nat -> Nat -> Real)
  (hnonneg : forall i j, 0 <= vertical i j) :
-- imply
  isingRectanglePrimitive horizontal vertical i j <= isingRectanglePrimitive horizontal vertical i (j + 1) := by
-- proof
  apply StatMech.Universality.isingRectanglePrimitive_vertical_mono_of_increment horizontal vertical hnonneg i j

/--
[isingRectangle_horizontal_increment_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectangle_horizontal_increment_sum_le_eq
  {C : Real}
-- given
  (horizontal vertical : Nat -> Nat -> Real)
  (hclosed : IsingRectangleClosedOneForm horizontal vertical)
  (width height : Nat)
  (hlower : ∀ i j, 0 ≤ isingRectanglePrimitive horizontal vertical i j)
  (hupper : ∀ i j, isingRectanglePrimitive horizontal vertical i j ≤ C) :
-- imply
  (∑ j ∈ range height, ∑ i ∈ range width, horizontal i j) ≤ height * C := by
-- proof
  apply StatMech.Universality.isingRectangle_horizontal_increment_sum_le horizontal vertical hclosed C width height hlower hupper

/--
[isingRectangle_vertical_increment_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectangle_vertical_increment_sum_le_eq
  {C : Real}
-- given
  (horizontal vertical : Nat -> Nat -> Real)
  (width height : Nat)
  (hlower : ∀ i j, 0 ≤ isingRectanglePrimitive horizontal vertical i j)
  (hupper : ∀ i j, isingRectanglePrimitive horizontal vertical i j ≤ C) :
-- imply
  (∑ i ∈ range width, ∑ j ∈ range height, vertical i j) ≤ width * C := by
-- proof
  apply StatMech.Universality.isingRectangle_vertical_increment_sum_le horizontal vertical C width height hlower hupper

/--
[isingRectangle_increment_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectangle_increment_sum_le_eq
  {C : Real}
-- given
  (horizontal vertical : Nat -> Nat -> Real)
  (hclosed : IsingRectangleClosedOneForm horizontal vertical)
  (width height : Nat)
  (hlower : ∀ i j, 0 ≤ isingRectanglePrimitive horizontal vertical i j)
  (hupper : ∀ i j, isingRectanglePrimitive horizontal vertical i j ≤ C) :
-- imply
  (∑ j ∈ range height, ∑ i ∈ range width, horizontal i j) + (∑ i ∈ range width, ∑ j ∈ range height, vertical i j) ≤ (height + width) * C := by
-- proof
  apply StatMech.Universality.isingRectangle_increment_sum_le horizontal vertical hclosed C width height hlower hupper

/--
[isingRectangle_scaled_increment_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectangle_scaled_increment_sum_le_eq
  {C mesh L : Real}
-- given
  (horizontal vertical : Nat -> Nat -> Real)
  (hclosed : IsingRectangleClosedOneForm horizontal vertical)
  (width height : Nat)
  (hlower : ∀ i j, 0 ≤ isingRectanglePrimitive horizontal vertical i j)
  (hupper : ∀ i j, isingRectanglePrimitive horizontal vertical i j ≤ C)
  (hmesh : 0 ≤ mesh)
  (hC : 0 ≤ C)
  (hscale : mesh * (height + width) ≤ L) :
-- imply
  mesh * ((∑ j ∈ range height, ∑ i ∈ range width, horizontal i j) + (∑ i ∈ range width, ∑ j ∈ range height, vertical i j)) ≤ L * C := by
-- proof
  apply StatMech.Universality.isingRectangle_scaled_increment_sum_le horizontal vertical hclosed C mesh L width height hlower hupper hmesh hC hscale

/--
[isingRectangle_scaled_normSq_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectangle_scaled_normSq_sum_le_eq
  {C mesh L : Real}
-- given
  (horizontalF verticalF : Nat -> Nat -> Complex)
  (hclosed : IsingRectangleClosedOneForm (fun i j => isingPrimitiveIncrement (horizontalF i j)) (fun i j => isingPrimitiveIncrement (verticalF i j)))
  (width height : Nat)
  (hlower : ∀ i j, 0 ≤ isingRectanglePrimitive (fun a b => isingPrimitiveIncrement (horizontalF a b)) (fun a b => isingPrimitiveIncrement (verticalF a b)) i j)
  (hupper : ∀ i j, isingRectanglePrimitive (fun a b => isingPrimitiveIncrement (horizontalF a b)) (fun a b => isingPrimitiveIncrement (verticalF a b)) i j ≤ C)
  (hmesh : 0 ≤ mesh)
  (hC : 0 ≤ C)
  (hscale : mesh * (height + width) ≤ L) :
-- imply
  mesh * ((∑ j ∈ range height, ∑ i ∈ range width, Complex.normSq (horizontalF i j)) + (∑ i ∈ range width, ∑ j ∈ range height, Complex.normSq (verticalF i j))) ≤ L * C := by
-- proof
  apply StatMech.Universality.isingRectangle_scaled_normSq_sum_le horizontalF verticalF hclosed C mesh L width height hlower hupper hmesh hC hscale

/--
[isingRectangle_physicalNormalized_normSq_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean)
-/
@[path]
private lemma isingRectangle_physicalNormalized_normSq_sum_le_eq
  {C mesh L : Real}
-- given
  (horizontalF verticalF : Nat -> Nat -> Complex)
  (hclosed : IsingRectangleClosedOneForm (fun i j => isingPrimitiveIncrement (horizontalF i j)) (fun i j => isingPrimitiveIncrement (verticalF i j)))
  (width height : Nat)
  (hlower : ∀ i j, 0 ≤ isingRectanglePrimitive (fun a b => isingPrimitiveIncrement (horizontalF a b)) (fun a b => isingPrimitiveIncrement (verticalF a b)) i j)
  (hupper : ∀ i j, isingRectanglePrimitive (fun a b => isingPrimitiveIncrement (horizontalF a b)) (fun a b => isingPrimitiveIncrement (verticalF a b)) i j ≤ C)
  (hmesh : 0 < mesh)
  (hC : 0 ≤ C)
  (hscale : mesh * (height + width) ≤ L) :
-- imply
  mesh ^ 2 * ((∑ j ∈ range height, ∑ i ∈ range width, Complex.normSq (horizontalF i j / (Real.sqrt (2 * mesh) : Complex))) + (∑ i ∈ range width, ∑ j ∈ range height, Complex.normSq (verticalF i j / (Real.sqrt (2 * mesh) : Complex)))) ≤ L * C / 2 := by
-- proof
  apply StatMech.Universality.isingRectangle_physicalNormalized_normSq_sum_le horizontalF verticalF hclosed C mesh L width height hlower hupper hmesh hC hscale


-- created on 2026-10-23
