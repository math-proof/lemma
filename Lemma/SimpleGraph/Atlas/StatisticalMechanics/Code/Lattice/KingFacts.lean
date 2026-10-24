import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.KingFacts
open SimpleGraph Function StatMech StatMech.Lattice


/--
[kf_hyperAdj_kingAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingFacts.lean)
-/
@[path]
private lemma kf_hyperAdj_kingAdj_eq
  {x y : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj x y) :
-- imply
  KingAdj x y := by
-- proof
  apply StatMech.Lattice.kf_hyperAdj_kingAdj x y h

/--
[kf_induce_le_kingGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingFacts.lean)
-/
@[path]
private lemma kf_induce_le_kingGraph_eq
  {K : Set (Site 2)} :
-- imply
  (hypercubicLattice 2).induce (Kᶜ : Set (Site 2)) ≤ boundaryKingGraph K := by
-- proof
  apply StatMech.Lattice.kf_induce_le_kingGraph K

/--
[kf_boundaryKingConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingFacts.lean)
-/
@[path]
private lemma kf_boundaryKingConnected_eq
  {K : Set (Site 2)} :
-- imply
  BoundaryKingConnected K := by
-- proof
  apply StatMech.Lattice.kf_boundaryKingConnected K

/--
[kf_cornerHead_king](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingFacts.lean)
-/
@[path]
private lemma kf_cornerHead_king_eq
  {e : Dart} :
-- imply
  KingAdj e.head (e.tail + (-rot90Fun e.dir)) := by
-- proof
  apply StatMech.Lattice.kf_cornerHead_king e

/--
[kf_dartNext_head_kingAdj_or_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingFacts.lean)
-/
@[path]
private lemma kf_dartNext_head_kingAdj_or_eq_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  (dartNext K e).head = e.head ∨ KingAdj e.head (dartNext K e).head := by
-- proof
  apply StatMech.Lattice.kf_dartNext_head_kingAdj_or_eq K e

/--
[kf_sameOrbit_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingFacts.lean)
-/
@[path]
private lemma kf_sameOrbit_step_eq
  {K : Set (Site 2)}
  {e d : Dart}
-- given
  (h : SameOrbit K e d) :
-- imply
  SameOrbit K e (dartNext K d) := by
-- proof
  apply StatMech.Lattice.kf_sameOrbit_step K h

/--
[kf_orbitKingTransport_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingFacts.lean)
-/
@[path]
private lemma kf_orbitKingTransport_step_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u : Site 2}
-- given
  (ho : OrbitReached K e u) :
-- imply
  ∃ v : Site 2, (v = u ∨ KingAdj u v) ∧ OrbitReached K e v := by
-- proof
  apply StatMech.Lattice.kf_orbitKingTransport_step K e ho

/--
[kf_interfaceConnected_of_orbitResidues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingFacts.lean)
-/
@[path]
private lemma kf_interfaceConnected_of_orbitResidues_eq
  {K : Set (Site 2)}
-- given
  (htr : OrbitKingTransport K)
  (hsat : OrbitVertexSaturate K) :
-- imply
  InterfaceConnected K := by
-- proof
  apply StatMech.Lattice.kf_interfaceConnected_of_orbitResidues K htr hsat


-- created on 2026-10-23
