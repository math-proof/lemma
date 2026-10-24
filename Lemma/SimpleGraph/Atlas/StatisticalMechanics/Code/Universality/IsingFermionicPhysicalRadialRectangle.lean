import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareInteriorRadialRectanglePlacement StatMech.Universality.FKIsingSquareInteriorRadialFiniteRectanglePlacement


/--
[increment_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialRectangle.lean)
-/
@[path]
private lemma increment_closed_eq
  {n : Nat}
  {hn : 0 < n}
  {P : FKIsingSquareInteriorRadialRectanglePlacement n hn} :
-- imply
  IsingRectangleClosedOneForm P.horizontalIncrement P.verticalIncrement := by
-- proof
  apply StatMech.Universality.FKIsingSquareInteriorRadialRectanglePlacement.increment_closed P

/--
[mk_representative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialRectangle.lean)
-/
@[path]
private lemma mk_representative_eq
  {n : Nat}
  {hn : 0 < n}
  {e : FKIsingSquareInteriorRadialIncidence n hn} :
-- imply
  Quot.mk _ (representative e) = e := by
-- proof
  apply StatMech.Universality.FKIsingSquareInteriorRadialRectanglePlacement.mk_representative e

/--
[primitiveIncrement_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialRectangle.lean)
-/
@[path]
private lemma primitiveIncrement_carrier_eq
  {n : Nat}
  {hn : 0 < n}
  {e : FKIsingSquareInteriorRadialIncidence n hn} :
-- imply
  fkIsingSquareWiredPrimitiveIncrement n hn (carrier e) = fkIsingSquareInteriorRadialIncrement n hn e := by
-- proof
  apply StatMech.Universality.FKIsingSquareInteriorRadialRectanglePlacement.primitiveIncrement_carrier e

/--
[carrier_increment_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialRectangle.lean)
-/
@[path]
private lemma carrier_increment_closed_eq
  {n : Nat}
  {hn : 0 < n}
  {P : FKIsingSquareInteriorRadialRectanglePlacement n hn} :
-- imply
  IsingRectangleClosedOneForm (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn (P.horizontalCarrier i j)) (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn (P.verticalCarrier i j)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareInteriorRadialRectanglePlacement.carrier_increment_closed P

/--
[physicalNormalized_normSq_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialRectangle.lean)
-/
@[path]
private lemma physicalNormalized_normSq_sum_le_eq
  {n : Nat}
  {hn : 0 < n}
  {P : FKIsingSquareInteriorRadialRectanglePlacement n hn}
  {C mesh L : Real}
-- given
  (width height : Nat)
  (hupper : ∀ i j, fkIsingSquareWiredIntegratedPrimitive n hn P.horizontalCarrier P.verticalCarrier i j ≤ C)
  (hmesh : 0 < mesh)
  (hC : 0 ≤ C)
  (hscale : mesh * (height + width) ≤ L) :
-- imply
  mesh ^ 2 * ((∑ j ∈ Finset.range height, ∑ i ∈ Finset.range width, Complex.normSq (fkIsingSquareWiredObservableGrid n hn P.horizontalCarrier i j / (Real.sqrt (2 * mesh) : Complex))) + (∑ i ∈ Finset.range width, ∑ j ∈ Finset.range height, Complex.normSq (fkIsingSquareWiredObservableGrid n hn P.verticalCarrier i j / (Real.sqrt (2 * mesh) : Complex)))) ≤ L * C / 2 := by
-- proof
  apply StatMech.Universality.FKIsingSquareInteriorRadialRectanglePlacement.physicalNormalized_normSq_sum_le P C mesh L width height hupper hmesh hC hscale

/--
[increment_closed_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialRectangle.lean)
-/
@[path]
private lemma increment_closed_on_eq
  {n width height : Nat}
  {hn : 0 < n}
  {P : FKIsingSquareInteriorRadialFiniteRectanglePlacement n hn width height} :
-- imply
  IsingRectangleClosedOneFormOn P.horizontalIncrement P.verticalIncrement width height := by
-- proof
  apply StatMech.Universality.FKIsingSquareInteriorRadialFiniteRectanglePlacement.increment_closed_on P

/--
[carrier_increment_closed_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialRectangle.lean)
-/
@[path]
private lemma carrier_increment_closed_on_eq
  {n width height : Nat}
  {hn : 0 < n}
  {P : FKIsingSquareInteriorRadialFiniteRectanglePlacement n hn width height} :
-- imply
  IsingRectangleClosedOneFormOn (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn (P.horizontalCarrier i j)) (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn (P.verticalCarrier i j)) width height := by
-- proof
  apply StatMech.Universality.FKIsingSquareInteriorRadialFiniteRectanglePlacement.carrier_increment_closed_on P

/--
[physicalNormalized_normSq_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialRectangle.lean)
-/
@[path]
private lemma physicalNormalized_normSq_sum_le_eq_2
  {n width height : Nat}
  {hn : 0 < n}
  {P : FKIsingSquareInteriorRadialFiniteRectanglePlacement n hn width height}
  {C mesh L : Real}
-- given
  (hupper : ∀ i ≤ width, ∀ j ≤ height, fkIsingSquareWiredIntegratedPrimitive n hn P.horizontalCarrier P.verticalCarrier i j ≤ C)
  (hmesh : 0 < mesh)
  (hC : 0 ≤ C)
  (hscale : mesh * (height + width) ≤ L) :
-- imply
  mesh ^ 2 * ((∑ j ∈ Finset.range height, ∑ i ∈ Finset.range width, Complex.normSq (fkIsingSquareWiredObservableGrid n hn P.horizontalCarrier i j / (Real.sqrt (2 * mesh) : Complex))) + (∑ i ∈ Finset.range width, ∑ j ∈ Finset.range height, Complex.normSq (fkIsingSquareWiredObservableGrid n hn P.verticalCarrier i j / (Real.sqrt (2 * mesh) : Complex)))) ≤ L * C / 2 := by
-- proof
  apply StatMech.Universality.FKIsingSquareInteriorRadialFiniteRectanglePlacement.physicalNormalized_normSq_sum_le P C mesh L hupper hmesh hC hscale


-- created on 2026-10-23
