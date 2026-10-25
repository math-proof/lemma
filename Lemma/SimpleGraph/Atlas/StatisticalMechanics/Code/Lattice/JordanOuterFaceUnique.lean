import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part3
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[outerBoxRadius_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOuterFaceUnique.lean)
-/
@[path]
private lemma outerBoxRadius_spec_eq
  {P : PlanarZ2Subgraph} :
-- imply
  ∀ v : P.V, P.emb v ∈ box 2 (outerBoxRadius P) := by
-- proof
  apply StatMech.Lattice.outerBoxRadius_spec P

/--
[exterior_in_outerRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOuterFaceUnique.lean)
-/
@[path]
private lemma exterior_in_outerRegion_eq
  {P : PlanarZ2Subgraph}
  {x : Site 2}
-- given
  (hx : x ∈ exterior 2 (outerBoxRadius P)) :
-- imply
  (regionGraph (imageGraph P)).connectedComponentMk x = outerRegion P := by
-- proof
  apply StatMech.Lattice.exterior_in_outerRegion P hx

/--
[outerRegion_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOuterFaceUnique.lean)
-/
@[path]
private lemma outerRegion_infinite_eq
  {P : PlanarZ2Subgraph} :
-- imply
  (outerRegion P).supp.Infinite := by
-- proof
  apply StatMech.Lattice.outerRegion_infinite P

/--
[infiniteComponent_meets_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOuterFaceUnique.lean)
-/
@[path]
private lemma infiniteComponent_meets_exterior_eq
  {P : PlanarZ2Subgraph}
  {C : (regionGraph (imageGraph P)).ConnectedComponent}
-- given
  (hC : C.supp.Infinite) :
-- imply
  ∃ x ∈ C.supp, x ∈ exterior 2 (outerBoxRadius P) := by
-- proof
  apply StatMech.Lattice.infiniteComponent_meets_exterior P hC

/--
[regionGraph_unique_infinite_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOuterFaceUnique.lean)
-/
@[path]
private lemma regionGraph_unique_infinite_component_eq
  {P : PlanarZ2Subgraph} :
-- imply
  ∃! C : (regionGraph (imageGraph P)).ConnectedComponent, C.supp.Infinite := by
-- proof
  apply StatMech.Lattice.regionGraph_unique_infinite_component P

/--
[outerRegion_eq_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOuterFaceUnique.lean)
-/
@[path]
private lemma outerRegion_eq_of_infinite_eq
  {P : PlanarZ2Subgraph}
  {C : (regionGraph (imageGraph P)).ConnectedComponent}
-- given
  (hC : C.supp.Infinite) :
-- imply
  C = outerRegion P := by
-- proof
  apply StatMech.Lattice.outerRegion_eq_of_infinite P hC

/--
[boundedRegion_iff_ne_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOuterFaceUnique.lean)
-/
@[path]
private lemma boundedRegion_iff_ne_outer_eq
  {P : PlanarZ2Subgraph}
  {C : (regionGraph (imageGraph P)).ConnectedComponent} :
-- imply
  C.supp.Finite ↔ C ≠ outerRegion P := by
-- proof
  apply StatMech.Lattice.boundedRegion_iff_ne_outer P C

/--
[geometricRegionCount_add_one_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOuterFaceUnique.lean)
-/
@[path]
private lemma geometricRegionCount_add_one_eq_card_eq
  {P : PlanarZ2Subgraph}
  [Empty.Finite (regionGraph (imageGraph P)).ConnectedComponent] :
-- imply
  geometricRegionCount P + 1 = Nat.card (regionGraph (imageGraph P)).ConnectedComponent := by
-- proof
  apply StatMech.Lattice.geometricRegionCount_add_one_eq_card P

/--
[faceCount_eq_boundedRegions_with_unique_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOuterFaceUnique.lean)
-/
@[path]
private lemma faceCount_eq_boundedRegions_with_unique_outer_eq
  {P : PlanarZ2Subgraph}
-- given
  (hJ : DiscreteJordanSeparation P) :
-- imply
  faceCount P.G = geometricRegionCount P + 1 ∧ (outerRegion P).supp.Infinite ∧ (∀ C : (regionGraph (imageGraph P)).ConnectedComponent, C.supp.Infinite → C = outerRegion P) ∧ (∀ C : (regionGraph (imageGraph P)).ConnectedComponent, C.supp.Finite ↔ C ≠ outerRegion P) := by
-- proof
  apply StatMech.Lattice.faceCount_eq_boundedRegions_with_unique_outer P hJ


-- created on 2026-10-23
