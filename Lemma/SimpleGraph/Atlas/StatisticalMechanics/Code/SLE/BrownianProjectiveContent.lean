import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.SLE.BrownianProjectiveContent
open Filter MeasureTheory Set Topology StatMech StatMech.SLE


/--
[brownianProjectiveContent_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProjectiveContent.lean)
-/
@[path]
private lemma brownianProjectiveContent_cylinder_eq
  {I : Finset Real}
-- given
  (S : Set (I -> Real))
  (hS : MeasurableSet S) :
-- imply
  brownianProjectiveContent (cylinder I S) = brownianFiniteDimensionalPiLaw I S := by
-- proof
  apply StatMech.SLE.brownianProjectiveContent_cylinder I S hS

/--
[brownianProjectiveContent_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProjectiveContent.lean)
-/
@[path]
private lemma brownianProjectiveContent_empty_eq :
-- imply
  brownianProjectiveContent (∅ : Set (Real -> Real)) = 0 := by
-- proof
  apply StatMech.SLE.brownianProjectiveContent_empty

/--
[brownianProjectiveContent_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProjectiveContent.lean)
-/
@[path]
private lemma brownianProjectiveContent_univ_eq :
-- imply
  brownianProjectiveContent (univ : Set (Real -> Real)) = 1 := by
-- proof
  apply StatMech.SLE.brownianProjectiveContent_univ

/--
[brownianProjectiveContent_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProjectiveContent.lean)
-/
@[path]
private lemma brownianProjectiveContent_ne_top_eq
-- given
  (A : Set (Real -> Real)) :
-- imply
  brownianProjectiveContent A ≠ ∞ := by
-- proof
  apply StatMech.SLE.brownianProjectiveContent_ne_top A

/--
[brownianProjectiveContent_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProjectiveContent.lean)
-/
@[path]
private lemma brownianProjectiveContent_mono_eq
  {A B : Set (Real -> Real)}
-- given
  (hA : A ∈ measurableCylinders fun _ : Real => Real)
  (hB : B ∈ measurableCylinders fun _ : Real => Real)
  (hAB : A <= B) :
-- imply
  brownianProjectiveContent A <= brownianProjectiveContent B := by
-- proof
  apply StatMech.SLE.brownianProjectiveContent_mono hA hB hAB

/--
[brownianProjectiveContent_iUnion_cylinder_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProjectiveContent.lean)
-/
@[path]
private lemma brownianProjectiveContent_iUnion_cylinder_le_eq
  {I : Finset Real}
-- given
  (S : Nat -> Set (I -> Real))
  (hS : forall n, MeasurableSet (S n)) :
-- imply
  brownianProjectiveContent (cylinder I (iUnion S)) <= tsum (fun n => brownianProjectiveContent (cylinder I (S n))) := by
-- proof
  apply StatMech.SLE.brownianProjectiveContent_iUnion_cylinder_le I S hS

/--
[brownianProjectiveContent_cylinder_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProjectiveContent.lean)
-/
@[path]
private lemma brownianProjectiveContent_cylinder_tendsto_zero_eq
  {I : Finset Real}
-- given
  (S : Nat -> Set (I -> Real))
  (hS : forall n, MeasurableSet (S n))
  (hanti : Antitone S)
  (hinter : iInter S = (∅ : Set (I -> Real))) :
-- imply
  Tendsto (fun n => brownianProjectiveContent (cylinder I (S n))) atTop (nhds 0) := by
-- proof
  apply StatMech.SLE.brownianProjectiveContent_cylinder_tendsto_zero I S hS hanti hinter

/--
[brownianProjectiveContent_cylinder_tendsto_zero_of_bounded_coordinates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProjectiveContent.lean)
-/
@[path]
private lemma brownianProjectiveContent_cylinder_tendsto_zero_of_bounded_coordinates_eq
  {J : Finset Real}
-- given
  (I : Nat -> Finset Real)
  (S : forall n, Set (I n -> Real))
  (hS : forall n, MeasurableSet (S n))
  (hIJ : forall n, I n <= J)
  (hanti : Antitone (fun n => Finset.restrict₂ (π := fun _ : Real => Real) (hIJ n) ⁻¹' S n))
  (hinter : iInter (fun n => Finset.restrict₂ (π := fun _ : Real => Real) (hIJ n) ⁻¹' S n) = (∅ : Set (J -> Real))) :
-- imply
  Tendsto (fun n => brownianProjectiveContent (cylinder (I n) (S n))) atTop (nhds 0) := by
-- proof
  apply StatMech.SLE.brownianProjectiveContent_cylinder_tendsto_zero_of_bounded_coordinates I S hS J hIJ hanti hinter


-- created on 2026-10-23
