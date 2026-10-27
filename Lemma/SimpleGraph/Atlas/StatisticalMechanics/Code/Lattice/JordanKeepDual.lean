import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepDual.Part4
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jkd_wall_not_mem_pushGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_wall_not_mem_pushGraph_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {x y : P.V}
-- given
  (hnotK : ¬ K.Adj x y) :
-- imply
  s(P.emb x, P.emb y) ∉ (jei_pushGraph P K).edgeSet := by
-- proof
  apply StatMech.Lattice.jkd_wall_not_mem_pushGraph P K hnotK

/--
[jkd_keepResidue_of_windingColoring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_keepResidue_of_windingColoring_eq
  {P : PlanarZ2Subgraph}
-- given
  (hres : whc_WhitneyColoringResidue) :
-- imply
  jwc_KeepResidue P := by
-- proof
  apply StatMech.Lattice.jkd_keepResidue_of_windingColoring hres P

/--
[jkd_faithfulDiscreteJordan_of_windingColoring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_faithfulDiscreteJordan_of_windingColoring_eq
  {P : PlanarZ2Subgraph}
-- given
  (hres : whc_WhitneyColoringResidue) :
-- imply
  whc_FaithfulDiscreteJordan P := by
-- proof
  apply StatMech.Lattice.jkd_faithfulDiscreteJordan_of_windingColoring hres P

/--
[jkd_latadj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_latadj_eq
  {a b : Site 2}
-- given
  (h : (∑ i, (a i - b i).natAbs) = 1) :
-- imply
  (hypercubicLattice 2).Adj a b := by
-- proof
  apply StatMech.Lattice.jkd_latadj h

/--
[jkd_faceRegion_botPush_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_faceRegion_botPush_adj_eq
  {P : PlanarZ2Subgraph}
  {a b : Site 2}
-- given
  (hlat : (hypercubicLattice 2).Adj a b) :
-- imply
  (whb_faceRegion (jei_pushGraph P ⊥)).Adj a b := by
-- proof
  apply StatMech.Lattice.jkd_faceRegion_botPush_adj P hlat

/--
[jkd_shared_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_shared_bottom_eq :
-- imply
  sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jbc_Pce.emb jbc_v0, jbc_Pce.emb jbc_v1) := by
-- proof
  apply StatMech.Lattice.jkd_shared_bottom

/--
[jkd_witness_square_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_witness_square_reach_eq :
-- imply
  ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.jkd_witness_square_reach

/--
[jkd_keepResidue_witness_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_keepResidue_witness_square_eq :
-- imply
  (⊥ : SimpleGraph jbc_Pce.V) ≤ jbc_Pce.G ∧ jbc_Pce.G.Adj jbc_v0 jbc_v1 ∧ ¬ (⊥ : SimpleGraph jbc_Pce.V).Adj jbc_v0 jbc_v1 ∧ (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jbc_Pce.emb jbc_v0, jbc_Pce.emb jbc_v1) ∧ ¬ (⊥ : SimpleGraph jbc_Pce.V).Reachable jbc_v0 jbc_v1 ∧ ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.jkd_keepResidue_witness_square

/--
[jkd_keepResidue_witness_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_keepResidue_witness_consistent_eq
-- given
  (hres : whc_WhitneyColoringResidue) :
-- imply
  ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.jkd_keepResidue_witness_consistent hres

/--
[jkd_gr9emb_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_gr9emb_inj_eq :
-- imply
  Function.Injective jkd_gr9emb := by
-- proof
  apply StatMech.Lattice.jkd_gr9emb_inj

/--
[jkd_gr9G_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_gr9G_adj_eq
  {i j : Fin 9} :
-- imply
  jkd_gr9G.Adj i j ↔ jkd_gr9rel i j := by
-- proof
  apply StatMech.Lattice.jkd_gr9G_adj i j

/--
[jkd_gr9_isSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_gr9_isSub_eq :
-- imply
  ∀ ⦃i j : Fin 9⦄, jkd_gr9G.Adj i j → (hypercubicLattice 2).Adj (jkd_gr9emb i) (jkd_gr9emb j) := by
-- proof
  apply StatMech.Lattice.jkd_gr9_isSub

/--
[jkd_r0_ne_r1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_r0_ne_r1_eq :
-- imply
  jkd_r0 ≠ jkd_r1 := by
-- proof
  apply StatMech.Lattice.jkd_r0_ne_r1

/--
[jkd_ring_centre_deg4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_ring_centre_deg4_eq :
-- imply
  jkd_gr9G.neighborSet 4 = {1, 3, 5, 7} := by
-- proof
  apply StatMech.Lattice.jkd_ring_centre_deg4

/--
[jkd_ring_Gadj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_ring_Gadj_eq :
-- imply
  jkd_ringP.G.Adj jkd_r0 jkd_r1 := by
-- proof
  apply StatMech.Lattice.jkd_ring_Gadj

/--
[jkd_ring_emb0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_ring_emb0_eq :
-- imply
  jkd_ringP.emb jkd_r0 = ![0, 0] := by
-- proof
  apply StatMech.Lattice.jkd_ring_emb0

/--
[jkd_ring_emb1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_ring_emb1_eq :
-- imply
  jkd_ringP.emb jkd_r1 = ![1, 0] := by
-- proof
  apply StatMech.Lattice.jkd_ring_emb1

/--
[jkd_ring_shared_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_ring_shared_bottom_eq :
-- imply
  sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) := by
-- proof
  apply StatMech.Lattice.jkd_ring_shared_bottom

/--
[jkd_ring_witness_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_ring_witness_reach_eq :
-- imply
  ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.jkd_ring_witness_reach

/--
[jkd_keepResidue_witness_ring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_keepResidue_witness_ring_eq :
-- imply
  (⊥ : SimpleGraph jkd_ringP.V) ≤ jkd_ringP.G ∧ jkd_ringP.G.Adj jkd_r0 jkd_r1 ∧ ¬ (⊥ : SimpleGraph jkd_ringP.V).Adj jkd_r0 jkd_r1 ∧ (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∧ ¬ (⊥ : SimpleGraph jkd_ringP.V).Reachable jkd_r0 jkd_r1 ∧ ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.jkd_keepResidue_witness_ring

/--
[jkd_keepResidue_witness_ring_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean)
-/
@[path]
private lemma jkd_keepResidue_witness_ring_consistent_eq
-- given
  (hres : whc_WhitneyColoringResidue) :
-- imply
  ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.jkd_keepResidue_witness_ring_consistent hres


-- created on 2026-10-23
