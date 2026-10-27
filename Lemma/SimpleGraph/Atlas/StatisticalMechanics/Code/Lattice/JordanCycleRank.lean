import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleRank.Part2
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jcr_regionComponents_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleRank.lean)
-/
@[path]
private lemma jcr_regionComponents_finite_eq
  {P : PlanarZ2Subgraph} :
-- imply
  Empty.Finite (regionGraph (imageGraph P)).ConnectedComponent := by
-- proof
  apply StatMech.Lattice.jcr_regionComponents_finite P

/--
[jcr_dual_of_discreteJordan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleRank.lean)
-/
@[path]
private lemma jcr_dual_of_discreteJordan_eq
  {P : PlanarZ2Subgraph}
-- given
  (h : DiscreteJordanSeparation P) :
-- imply
  jcr_DualEulerCount P := by
-- proof
  apply StatMech.Lattice.jcr_dual_of_discreteJordan P h

/--
[jcr_geometricRegionCount_eq_nullity_of_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleRank.lean)
-/
@[path]
private lemma jcr_geometricRegionCount_eq_nullity_of_dual_eq
  {P : PlanarZ2Subgraph}
-- given
  (h : jcr_DualEulerCount P) :
-- imply
  geometricRegionCount P = nullity P.G := by
-- proof
  apply StatMech.Lattice.jcr_geometricRegionCount_eq_nullity_of_dual P h

/--
[jcr_discreteJordan_of_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleRank.lean)
-/
@[path]
private lemma jcr_discreteJordan_of_dual_eq
  {P : PlanarZ2Subgraph}
-- given
  (h : jcr_DualEulerCount P) :
-- imply
  DiscreteJordanSeparation P := by
-- proof
  apply StatMech.Lattice.jcr_discreteJordan_of_dual P h

/--
[jcr_discreteJordan_iff_dualEulerCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleRank.lean)
-/
@[path]
private lemma jcr_discreteJordan_iff_dualEulerCount_eq
  {P : PlanarZ2Subgraph} :
-- imply
  DiscreteJordanSeparation P ↔ jcr_DualEulerCount P := by
-- proof
  apply StatMech.Lattice.jcr_discreteJordan_iff_dualEulerCount P

/--
[jcr_faceCount_eq_geometric_regions_of_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleRank.lean)
-/
@[path]
private lemma jcr_faceCount_eq_geometric_regions_of_dual_eq
  {P : PlanarZ2Subgraph}
-- given
  (h : jcr_DualEulerCount P) :
-- imply
  faceCount P.G = geometricRegionCount P + 1 := by
-- proof
  apply StatMech.Lattice.jcr_faceCount_eq_geometric_regions_of_dual P h

/--
[jcr_euler_geometric_regions_of_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleRank.lean)
-/
@[path]
private lemma jcr_euler_geometric_regions_of_dual_eq
  {P : PlanarZ2Subgraph}
-- given
  (h : jcr_DualEulerCount P) :
-- imply
  (Nat.card P.V : ℤ) - P.G.edgeSet.ncard + (geometricRegionCount P + 1) = 1 + Nat.card P.G.ConnectedComponent := by
-- proof
  apply StatMech.Lattice.jcr_euler_geometric_regions_of_dual P h

/--
[jcr_imageGraph_bot_of_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleRank.lean)
-/
@[path]
private lemma jcr_imageGraph_bot_of_bot_eq
  {P : PlanarZ2Subgraph}
-- given
  (hG : P.G = ⊥) :
-- imply
  imageGraph P = ⊥ := by
-- proof
  apply StatMech.Lattice.jcr_imageGraph_bot_of_bot hG

/--
[jcr_regionGraph_adj_eq_lattice_of_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleRank.lean)
-/
@[path]
private lemma jcr_regionGraph_adj_eq_lattice_of_bot_eq
  {P : PlanarZ2Subgraph}
  {f g : Site 2}
-- given
  (hG : P.G = ⊥) :
-- imply
  (regionGraph (imageGraph P)).Adj f g ↔ (hypercubicLattice 2).Adj f g := by
-- proof
  apply StatMech.Lattice.jcr_regionGraph_adj_eq_lattice_of_bot hG f g

/--
[jcr_regionComponents_card_one_of_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleRank.lean)
-/
@[path]
private lemma jcr_regionComponents_card_one_of_bot_eq
  {P : PlanarZ2Subgraph}
-- given
  (hG : P.G = ⊥) :
-- imply
  Nat.card (regionGraph (imageGraph P)).ConnectedComponent = 1 := by
-- proof
  apply StatMech.Lattice.jcr_regionComponents_card_one_of_bot hG

/--
[jcr_emptyGraph_dualEulerCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleRank.lean)
-/
@[path]
private lemma jcr_emptyGraph_dualEulerCount_eq
  {P : PlanarZ2Subgraph}
-- given
  (hG : P.G = ⊥) :
-- imply
  jcr_DualEulerCount P := by
-- proof
  apply StatMech.Lattice.jcr_emptyGraph_dualEulerCount hG

/--
[jcr_discreteJordan_of_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleRank.lean)
-/
@[path]
private lemma jcr_discreteJordan_of_bot_eq
  {P : PlanarZ2Subgraph}
-- given
  (hG : P.G = ⊥) :
-- imply
  DiscreteJordanSeparation P := by
-- proof
  apply StatMech.Lattice.jcr_discreteJordan_of_bot hG


-- created on 2026-10-23
