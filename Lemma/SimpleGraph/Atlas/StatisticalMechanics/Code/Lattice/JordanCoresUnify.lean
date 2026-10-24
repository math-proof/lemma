import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanCoresUnify
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[jcu_walk_crosses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCoresUnify.lean)
-/
@[path]
private lemma jcu_walk_crosses_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S) :
-- imply
  ∃ e ∈ w.edges, bdEdge S e := by
-- proof
  apply StatMech.Lattice.jcu_walk_crosses S hx hy w

/--
[jcu_walk_meets_innerBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCoresUnify.lean)
-/
@[path]
private lemma jcu_walk_meets_innerBoundary_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S) :
-- imply
  ∃ u v : Site 2, u ∈ w.support ∧ v ∈ w.support ∧ (hypercubicLattice 2).Adj u v ∧ u ∈ S ∧ v ∉ S := by
-- proof
  apply StatMech.Lattice.jcu_walk_meets_innerBoundary S hx hy w

/--
[jcu_separatingSide_forces_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCoresUnify.lean)
-/
@[path]
private lemma jcu_separatingSide_forces_cross_eq
  {D B inside outside : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : jcu_HasSeparatingSide D B inside outside)
  (hx : x ∈ inside)
  (hy : y ∈ outside)
  (hwD : ∀ z ∈ w.support, z ∈ D) :
-- imply
  ∃ z ∈ w.support, z ∈ B := by
-- proof
  apply StatMech.Lattice.jcu_separatingSide_forces_cross h hx hy w hwD

/--
[jcu_floodFill_separatingSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCoresUnify.lean)
-/
@[path]
private lemma jcu_floodFill_separatingSide_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
  {xB : Site 2}
  {x y : Site 2}
-- given
  (hxB : xB ∈ rect m m' c d)
  (hx : x ∈ rect α β c d)
  (hxα : x 0 = α)
  (hii : y ∉ arcS_leftRegion ω α β m m' c d xB hxB) :
-- imply
  jcu_HasSeparatingSide (rect α β c d) (overlapComp ω m m' c d xB hxB) {x} {y} := by
-- proof
  apply StatMech.Lattice.jcu_floodFill_separatingSide ω α β m m' c d xB hxB hx hxα hii

/--
[jcu_discreteJordan_imp_twoPathsCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCoresUnify.lean)
-/
@[path]
private lemma jcu_discreteJordan_imp_twoPathsCross_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
  {xB : Site 2}
-- given
  (hxB : xB ∈ rect m m' c d)
  (hii : ∀ y : Site 2, y ∈ rect α β c d → y 0 = β → y ∉ arcS_leftRegion ω α β m m' c d xB hxB) :
-- imply
  ArcS_TwoPathsCross ω α β m m' c d xB hxB := by
-- proof
  apply StatMech.Lattice.jcu_discreteJordan_imp_twoPathsCross ω α β m m' c d xB hxB hii

/--
[jcu_interface_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCoresUnify.lean)
-/
@[path]
private lemma jcu_interface_separation_eq
  {K : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x ∈ K)
  (hy : y ∉ K) :
-- imply
  ∃ e ∈ w.edges, bdEdge K e := by
-- proof
  apply StatMech.Lattice.jcu_interface_separation K hx hy w

/--
[jcu_discreteJordan_imp_interfaceConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCoresUnify.lean)
-/
@[path]
private lemma jcu_discreteJordan_imp_interfaceConnected_eq
  {K : Set (Site 2)}
-- given
  (htr : OrbitKingTransport K)
  (hcon : BoundaryKingConnected K)
  (hsat : OrbitVertexSaturate K) :
-- imply
  InterfaceConnected K := by
-- proof
  apply StatMech.Lattice.jcu_discreteJordan_imp_interfaceConnected K htr hcon hsat

/--
[jcu_discreteJordan_imp_orbitFaceNoPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCoresUnify.lean)
-/
@[path]
private lemma jcu_discreteJordan_imp_orbitFaceNoPinch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hsimple : ∀ i ∈ Set.Iio (dartOrbitPeriod K a), ∀ j ∈ Set.Iio (dartOrbitPeriod K a), dartFace ((dartNext K)^[i] a.1) = dartFace ((dartNext K)^[j] a.1) → (dartNext K)^[i] a.1 = (dartNext K)^[j] a.1) :
-- imply
  OrbitFaceNoPinch K a := by
-- proof
  apply StatMech.Lattice.jcu_discreteJordan_imp_orbitFaceNoPinch K a hsimple

/--
[jcu_orbitFaceNoPinch_imp_simple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCoresUnify.lean)
-/
@[path]
private lemma jcu_orbitFaceNoPinch_imp_simple_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {i j : ℕ}
-- given
  (h : OrbitFaceNoPinch K a)
  (hi : i ∈ Set.Iio (dartOrbitPeriod K a))
  (hj : j ∈ Set.Iio (dartOrbitPeriod K a))
  (hface : dartFace ((dartNext K)^[i] a.1) = dartFace ((dartNext K)^[j] a.1)) :
-- imply
  (dartNext K)^[i] a.1 = (dartNext K)^[j] a.1 := by
-- proof
  apply StatMech.Lattice.jcu_orbitFaceNoPinch_imp_simple K a h hi hj hface

/--
[jcu_orbitFaceNoPinch_imp_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCoresUnify.lean)
-/
@[path]
private lemma jcu_orbitFaceNoPinch_imp_injOn_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : OrbitFaceNoPinch K a) :
-- imply
  Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) := by
-- proof
  apply StatMech.Lattice.jcu_orbitFaceNoPinch_imp_injOn K a h

/--
[jcu_twoPathsCross_of_floodFill_ii](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCoresUnify.lean)
-/
@[path]
private lemma jcu_twoPathsCross_of_floodFill_ii_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
  {xB : Site 2}
-- given
  (hxB : xB ∈ rect m m' c d)
  (hii : ∀ y : Site 2, y ∈ rect α β c d → y 0 = β → y ∉ arcS_leftRegion ω α β m m' c d xB hxB) :
-- imply
  ArcS_TwoPathsCross ω α β m m' c d xB hxB := by
-- proof
  apply StatMech.Lattice.jcu_twoPathsCross_of_floodFill_ii ω α β m m' c d xB hxB hii


-- created on 2026-10-23
