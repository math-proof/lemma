import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanVeblenPeel
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jvp_not_isAcyclic_of_even_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenPeel.lean)
-/
@[path]
private lemma jvp_not_isAcyclic_of_even_nonempty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (heven : ∀ v, Even (G.degree v))
  (hne : G.edgeSet.Nonempty) :
-- imply
  ¬ G.IsAcyclic := by
-- proof
  apply StatMech.Lattice.jvp_not_isAcyclic_of_even_nonempty G heven hne

/--
[jvp_exists_nonbridge_edge_of_even_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenPeel.lean)
-/
@[path]
private lemma jvp_exists_nonbridge_edge_of_even_nonempty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (heven : ∀ v, Even (G.degree v))
  (hne : G.edgeSet.Nonempty) :
-- imply
  ∃ a b : V, G.Adj a b ∧ (G.deleteEdges {s(a, b)}).Reachable a b := by
-- proof
  apply StatMech.Lattice.jvp_exists_nonbridge_edge_of_even_nonempty G heven hne

/--
[jvp_one_le_nullity_of_even_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenPeel.lean)
-/
@[path]
private lemma jvp_one_le_nullity_of_even_nonempty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (heven : ∀ v, Even (G.degree v))
  (hne : G.edgeSet.Nonempty) :
-- imply
  1 ≤ nullity G := by
-- proof
  apply StatMech.Lattice.jvp_one_le_nullity_of_even_nonempty G heven hne

/--
[jvp_abstract_even_of_closedContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenPeel.lean)
-/
@[path]
private lemma jvp_abstract_even_of_closedContour_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  [DecidableRel K.Adj]
-- given
  (hKle : K ≤ P.G)
  (hcc : jce_ClosedContour (jei_pushGraph P K).edgeSet) :
-- imply
  ∀ v : P.V, Even (Nat.card (K.neighborSet v)) := by
-- proof
  apply StatMech.Lattice.jvp_abstract_even_of_closedContour P K hKle hcc

/--
[jvp_evenPeel_of_steps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenPeel.lean)
-/
@[path]
private lemma jvp_evenPeel_of_steps_eq
  {P : PlanarZ2Subgraph}
-- given
  (hveb : jvp_VeblenStep P)
  (hreg : jvp_RegionStep P) :
-- imply
  jcx_EvenPeel P := by
-- proof
  apply StatMech.Lattice.jvp_evenPeel_of_steps P hveb hreg

/--
[jvp_faithfulCountResidue_of_steps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenPeel.lean)
-/
@[path]
private lemma jvp_faithfulCountResidue_of_steps_eq
-- given
  (h : ∀ (P : PlanarZ2Subgraph), jeb_EvenDegreeSubgraph P → jvp_VeblenStep P ∧ jvp_RegionStep P) :
-- imply
  jeb_FaithfulCountResidue := by
-- proof
  apply StatMech.Lattice.jvp_faithfulCountResidue_of_steps h

/--
[jvp_veblenStep_unitSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenPeel.lean)
-/
@[path]
private lemma jvp_veblenStep_unitSquare_eq :
-- imply
  jvp_VeblenStep jbc_Pce := by
-- proof
  apply StatMech.Lattice.jvp_veblenStep_unitSquare

/--
[jvp_regionStep_unitSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenPeel.lean)
-/
@[path]
private lemma jvp_regionStep_unitSquare_eq :
-- imply
  jvp_RegionStep jbc_Pce := by
-- proof
  apply StatMech.Lattice.jvp_regionStep_unitSquare

/--
[jvp_faithfulDiscreteJordan_unitSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenPeel.lean)
-/
@[path]
private lemma jvp_faithfulDiscreteJordan_unitSquare_eq :
-- imply
  whc_FaithfulDiscreteJordan jbc_Pce := by
-- proof
  apply StatMech.Lattice.jvp_faithfulDiscreteJordan_unitSquare

/--
[jvp_faceCount_deleteEdges_nonbridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenPeel.lean)
-/
@[path]
private lemma jvp_faceCount_deleteEdges_nonbridge_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (hab : G.Adj a b)
  (hr : (G.deleteEdges {s(a, b)}).Reachable a b) :
-- imply
  faceCount (G.deleteEdges {s(a, b)}) + 1 = faceCount G := by
-- proof
  apply StatMech.Lattice.jvp_faceCount_deleteEdges_nonbridge G hab hr

/--
[jvp_summary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenPeel.lean)
-/
@[path]
private lemma jvp_summary_eq :
-- imply
  (∀ (P : PlanarZ2Subgraph), jvp_VeblenStep P → jvp_RegionStep P → jcx_EvenPeel P) ∧ (jvp_VeblenStep jbc_Pce ∧ jvp_RegionStep jbc_Pce) ∧ whc_FaithfulDiscreteJordan jbc_Pce := by
-- proof
  apply StatMech.Lattice.jvp_summary


-- created on 2026-10-23
