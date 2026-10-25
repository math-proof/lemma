import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanGeneralCount.Part5
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jgc_leaf_deleteEdges_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_leaf_deleteEdges_isolated_eq
  {K : SimpleGraph V}
  {x z : V}
-- given
  (huniq : ∀ w, K.Adj x w → w = z) :
-- imply
  ∀ w, ¬ (K.deleteEdges {s(x, z)}).Adj x w := by
-- proof
  apply StatMech.Lattice.jgc_leaf_deleteEdges_isolated huniq

/--
[jgc_leaf_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_leaf_not_reachable_eq
  {K : SimpleGraph V}
  {x z : V}
-- given
  (hadj : K.Adj x z)
  (huniq : ∀ w, K.Adj x w → w = z) :
-- imply
  ¬ (K.deleteEdges {s(x, z)}).Reachable x z := by
-- proof
  apply StatMech.Lattice.jgc_leaf_not_reachable hadj huniq

/--
[jgc_faceCount_deleteLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_faceCount_deleteLeaf_eq
  [Empty.Finite V]
  [DecidableEq V]
  {K : SimpleGraph V}
  {x z : V}
-- given
  (hadj : K.Adj x z)
  (huniq : ∀ w, K.Adj x w → w = z) :
-- imply
  faceCount (K.deleteEdges {s(x, z)}) = faceCount K := by
-- proof
  apply StatMech.Lattice.jgc_faceCount_deleteLeaf K hadj huniq

/--
[jgc_tc_deleteLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_tc_deleteLeaf_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {x z : P.V}
-- given
  (hKle : K ≤ P.G)
  (hadj : K.Adj x z)
  (huniq : ∀ w, K.Adj x w → w = z) :
-- imply
  jic_tc P (K.deleteEdges {s(x, z)}) = jic_tc P K := by
-- proof
  apply StatMech.Lattice.jgc_tc_deleteLeaf P K hKle hadj huniq

/--
[jgc_tc_eq_faceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_tc_eq_faceCount_eq
  {P : PlanarZ2Subgraph} :
-- imply
  ∀ {K : SimpleGraph P.V}, jgc_IsCactus K → K ≤ P.G → jic_tc P K = faceCount K := by
-- proof
  apply StatMech.Lattice.jgc_tc_eq_faceCount P

/--
[jgc_total_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_total_count_eq
  {P : PlanarZ2Subgraph}
-- given
  (hcac : jgc_IsCactus P.G) :
-- imply
  Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent = faceCount P.G := by
-- proof
  apply StatMech.Lattice.jgc_total_count P hcac

/--
[jgc_faithfulRegionCount_eq_nullity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_faithfulRegionCount_eq_nullity_eq
  {P : PlanarZ2Subgraph}
-- given
  (hcac : jgc_IsCactus P.G) :
-- imply
  whc_faithfulRegionCount P = nullity P.G := by
-- proof
  apply StatMech.Lattice.jgc_faithfulRegionCount_eq_nullity P hcac

/--
[jgc_faithfulDiscreteJordan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_faithfulDiscreteJordan_eq
  {P : PlanarZ2Subgraph}
-- given
  (hcac : jgc_IsCactus P.G) :
-- imply
  whc_FaithfulDiscreteJordan P := by
-- proof
  apply StatMech.Lattice.jgc_faithfulDiscreteJordan P hcac

/--
[jgc_isCactus_of_isCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_isCactus_of_isCycles_eq
  [Empty.Finite V]
  [DecidableEq V]
  {K : SimpleGraph V}
-- given
  (hcyc : K.IsCycles) :
-- imply
  jgc_IsCactus K := by
-- proof
  apply StatMech.Lattice.jgc_isCactus_of_isCycles K hcyc

/--
[jgc_isCactus_of_isAcyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_isCactus_of_isAcyclic_eq
  [Empty.Finite V]
  [DecidableEq V]
  {K : SimpleGraph V}
-- given
  (hacyc : K.IsAcyclic) :
-- imply
  jgc_IsCactus K := by
-- proof
  apply StatMech.Lattice.jgc_isCactus_of_isAcyclic K hacyc

/--
[jgc_pend_emb_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_pend_emb_inj_eq :
-- imply
  Function.Injective jgc_pend_emb := by
-- proof
  apply StatMech.Lattice.jgc_pend_emb_inj

/--
[jgc_pend_G_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_pend_G_adj_eq
  {i j : Fin 5} :
-- imply
  jgc_pend_G.Adj i j ↔ jgc_pend_rel i j := by
-- proof
  apply StatMech.Lattice.jgc_pend_G_adj i j

/--
[jgc_pend_isSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_pend_isSub_eq :
-- imply
  ∀ ⦃i j : Fin 5⦄, jgc_pend_G.Adj i j → (hypercubicLattice 2).Adj (jgc_pend_emb i) (jgc_pend_emb j) := by
-- proof
  apply StatMech.Lattice.jgc_pend_isSub

/--
[jgc_pend_core_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_pend_core_adj_eq
  {i j : Fin 5} :
-- imply
  jgc_pend_core.Adj i j ↔ ((i == 0 && j == 1) || (i == 1 && j == 0) || (i == 1 && j == 2) || (i == 2 && j == 1) || (i == 2 && j == 3) || (i == 3 && j == 2) || (i == 3 && j == 0) || (i == 0 && j == 3) : Bool) := by
-- proof
  apply StatMech.Lattice.jgc_pend_core_adj i j

/--
[jgc_pend_leaf_uniq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_pend_leaf_uniq_eq :
-- imply
  ∀ w, jgc_pend_G.Adj 4 w → w = 0 := by
-- proof
  apply StatMech.Lattice.jgc_pend_leaf_uniq

/--
[jgc_pend_leaf_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_pend_leaf_adj_eq :
-- imply
  jgc_pend_G.Adj 4 0 := by
-- proof
  apply StatMech.Lattice.jgc_pend_leaf_adj

/--
[jgc_pend_delete_eq_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_pend_delete_eq_core_eq :
-- imply
  jgc_pend_G.deleteEdges {s((4 : Fin 5), 0)} = jgc_pend_core := by
-- proof
  apply StatMech.Lattice.jgc_pend_delete_eq_core

/--
[jgc_pend_core_isCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_pend_core_isCycles_eq :
-- imply
  jgc_pend_core.IsCycles := by
-- proof
  apply StatMech.Lattice.jgc_pend_core_isCycles

/--
[jgc_pend_isCactus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_pend_isCactus_eq :
-- imply
  jgc_IsCactus jgc_pend_G := by
-- proof
  apply StatMech.Lattice.jgc_pend_isCactus

/--
[jgc_pend_not_isCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_pend_not_isCycles_eq :
-- imply
  ¬ jgc_pend_G.IsCycles := by
-- proof
  apply StatMech.Lattice.jgc_pend_not_isCycles

/--
[jgc_faithfulDiscreteJordan_pendantSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean)
-/
@[path]
private lemma jgc_faithfulDiscreteJordan_pendantSquare_eq :
-- imply
  whc_FaithfulDiscreteJordan jgc_pend_P := by
-- proof
  apply StatMech.Lattice.jgc_faithfulDiscreteJordan_pendantSquare


-- created on 2026-10-23
