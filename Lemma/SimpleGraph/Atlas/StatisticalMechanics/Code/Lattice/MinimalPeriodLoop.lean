import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[mpl_orbitFaceLoop_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_orbitFaceLoop_length_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (mpl_orbitFaceLoop K a).length = dartOrbitPeriod K a := by
-- proof
  apply StatMech.Lattice.mpl_orbitFaceLoop_length K a

/--
[mpl_orbitFaceLoop_length_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_orbitFaceLoop_length_pos_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  0 < (mpl_orbitFaceLoop K a).length := by
-- proof
  apply StatMech.Lattice.mpl_orbitFaceLoop_length_pos K hK a

/--
[mpl_orbitFaceLoop_edges_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_orbitFaceLoop_edges_bdEdge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f g : Site 2}
-- given
  (h : s(f, g) ∈ (mpl_orbitFaceLoop K a).edges) :
-- imply
  bdEdge K (sharedPrimalEdge f g) := by
-- proof
  apply StatMech.Lattice.mpl_orbitFaceLoop_edges_bdEdge K a h

/--
[mpl_orbitLoop_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_orbitLoop_support_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (mpl_orbitLoop K a).support = (mpl_orbitFaceLoop K a).support := by
-- proof
  apply StatMech.Lattice.mpl_orbitLoop_support K a

/--
[mpl_orbitLoop_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_orbitLoop_edges_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (mpl_orbitLoop K a).edges = (mpl_orbitFaceLoop K a).edges := by
-- proof
  apply StatMech.Lattice.mpl_orbitLoop_edges K a

/--
[mpl_orbitLoop_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_orbitLoop_length_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (mpl_orbitLoop K a).length = dartOrbitPeriod K a := by
-- proof
  apply StatMech.Lattice.mpl_orbitLoop_length K a

/--
[mpl_orbitLoop_length_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_orbitLoop_length_pos_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  0 < (mpl_orbitLoop K a).length := by
-- proof
  apply StatMech.Lattice.mpl_orbitLoop_length_pos K hK a

/--
[mpl_orbitLoop_edges_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_orbitLoop_edges_bdEdge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f g : Site 2}
-- given
  (h : s(f, g) ∈ (mpl_orbitLoop K a).edges) :
-- imply
  bdEdge K (sharedPrimalEdge f g) := by
-- proof
  apply StatMech.Lattice.mpl_orbitLoop_edges_bdEdge K a h

/--
[mpl_orbitFaceLoop_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_orbitFaceLoop_isCycle_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
-- imply
  (mpl_orbitFaceLoop K a).IsCycle := by
-- proof
  apply StatMech.Lattice.mpl_orbitFaceLoop_isCycle K a hp hinj

/--
[mpl_orbitLoop_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_orbitLoop_isCycle_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
-- imply
  (mpl_orbitLoop K a).IsCycle := by
-- proof
  apply StatMech.Lattice.mpl_orbitLoop_isCycle K a hp hinj

/--
[mpl_dartFace_ucDart0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_dartFace_ucDart0_eq :
-- imply
  dartFace ucDart0 = ![0, 0] := by
-- proof
  apply StatMech.Lattice.mpl_dartFace_ucDart0

/--
[mpl_dartFace_ucDart1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_dartFace_ucDart1_eq :
-- imply
  dartFace ucDart1 = ![0, -1] := by
-- proof
  apply StatMech.Lattice.mpl_dartFace_ucDart1

/--
[mpl_dartFace_ucDart2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_dartFace_ucDart2_eq :
-- imply
  dartFace ucDart2 = ![-1, -1] := by
-- proof
  apply StatMech.Lattice.mpl_dartFace_ucDart2

/--
[mpl_dartFace_ucDart3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_dartFace_ucDart3_eq :
-- imply
  dartFace ucDart3 = ![-1, 0] := by
-- proof
  apply StatMech.Lattice.mpl_dartFace_ucDart3

/--
[mpl_dartFace_iterate_ucDart0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_dartFace_iterate_ucDart0_eq :
-- imply
  dartFace ((dartNext unitCell)^[0] ucDart0) = (![0, 0] : Site 2) := by
-- proof
  apply StatMech.Lattice.mpl_dartFace_iterate_ucDart0

/--
[mpl_dartFace_iterate_ucDart1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_dartFace_iterate_ucDart1_eq :
-- imply
  dartFace ((dartNext unitCell)^[1] ucDart0) = (![0, -1] : Site 2) := by
-- proof
  apply StatMech.Lattice.mpl_dartFace_iterate_ucDart1

/--
[mpl_dartFace_iterate_ucDart2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_dartFace_iterate_ucDart2_eq :
-- imply
  dartFace ((dartNext unitCell)^[2] ucDart0) = (![-1, -1] : Site 2) := by
-- proof
  apply StatMech.Lattice.mpl_dartFace_iterate_ucDart2

/--
[mpl_dartFace_iterate_ucDart3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_dartFace_iterate_ucDart3_eq :
-- imply
  dartFace ((dartNext unitCell)^[3] ucDart0) = (![-1, 0] : Site 2) := by
-- proof
  apply StatMech.Lattice.mpl_dartFace_iterate_ucDart3

/--
[mpl_dartFace_iterate_ucDart4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_dartFace_iterate_ucDart4_eq :
-- imply
  dartFace ((dartNext unitCell)^[4] ucDart0) = (![0, 0] : Site 2) := by
-- proof
  apply StatMech.Lattice.mpl_dartFace_iterate_ucDart4

/--
[mpl_unitCell_faceLoop_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_unitCell_faceLoop_edges_eq :
-- imply
  (mpl_orbitFaceLoop unitCell ucBase).edges = [s((![0, 0] : Site 2), ![0, -1]), s((![0, -1] : Site 2), ![-1, -1]), s((![-1, -1] : Site 2), ![-1, 0]), s((![-1, 0] : Site 2), ![0, 0])] := by
-- proof
  apply StatMech.Lattice.mpl_unitCell_faceLoop_edges

/--
[mpl_unitCell_rayCount_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_unitCell_rayCount_eq_one_eq :
-- imply
  jec_rayCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell ucBase) = 1 := by
-- proof
  apply StatMech.Lattice.mpl_unitCell_rayCount_eq_one

/--
[mpl_unitCell_tailOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean)
-/
@[path]
private lemma mpl_unitCell_tailOdd_eq :
-- imply
  ∃ i : ℕ, ¬ Even (jec_rayCount ((dartNext unitCell)^[i] ucBase.1).tail (mpl_orbitLoop unitCell ucBase)) := by
-- proof
  apply StatMech.Lattice.mpl_unitCell_tailOdd


-- created on 2026-10-23
