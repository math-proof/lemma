import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TriHexTorusDuality
open Finset Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangularTorusStep_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma triangularTorusStep_ne_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {i : Fin 3} :
-- imply
  triangularTorusStep L i ≠ 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorusStep_ne_zero L i

/--
[triangularTorusStep_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma triangularTorusStep_injective_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Function.Injective (triangularTorusStep L) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorusStep_injective L

/--
[triangularTorusStep_add_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma triangularTorusStep_add_ne_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {i j : Fin 3} :
-- imply
  triangularTorusStep L i + triangularTorusStep L j ≠ 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorusStep_add_ne_zero L i j

/--
[hexagonalTorusStep_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma hexagonalTorusStep_ne_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {i : Fin 3} :
-- imply
  hexagonalTorusStep L i ≠ 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusStep_ne_zero L i

/--
[hexagonalTorusStep_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma hexagonalTorusStep_injective_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Function.Injective (hexagonalTorusStep L) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusStep_injective L

/--
[triangularTorusIndexedEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma triangularTorusIndexedEdge_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a : TriHexTorusEdgeIndex L} :
-- imply
  triangularTorusIndexedEdge L a ∈ (triangularTorusGraph L).edgeSet := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorusIndexedEdge_mem L a

/--
[triangularTorusEdgeChart_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma triangularTorusEdgeChart_injective_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Function.Injective (triangularTorusEdgeChart L) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorusEdgeChart_injective L

/--
[triangularTorusEdgeChart_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma triangularTorusEdgeChart_surjective_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Function.Surjective (triangularTorusEdgeChart L) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorusEdgeChart_surjective L

/--
[hexagonalTorusIndexedEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma hexagonalTorusIndexedEdge_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a : TriHexTorusEdgeIndex L} :
-- imply
  hexagonalTorusIndexedEdge L a ∈ (hexagonalTorusGraph L).edgeSet := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusIndexedEdge_mem L a

/--
[hexagonalTorusEdgeChart_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma hexagonalTorusEdgeChart_injective_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Function.Injective (hexagonalTorusEdgeChart L) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusEdgeChart_injective L

/--
[hexagonalTorusEdgeChart_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma hexagonalTorusEdgeChart_surjective_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Function.Surjective (hexagonalTorusEdgeChart L) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusEdgeChart_surjective L

/--
[triHexTorusPrimalOfDualEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma triHexTorusPrimalOfDualEdge_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {e : Sym2 (HexTorusVertex L)}
-- given
  (he : e ∈ (hexagonalTorusGraph L).edgeFinset) :
-- imply
  triHexTorusPrimalOfDualEdge L e ∈ (triangularTorusGraph L).edgeFinset := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusPrimalOfDualEdge_mem L he

/--
[triHexTorusPrimalOfDualEdge_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma triHexTorusPrimalOfDualEdge_injOn_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Set.InjOn (triHexTorusPrimalOfDualEdge L) (↑(hexagonalTorusGraph L).edgeFinset : Set (Sym2 (HexTorusVertex L))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusPrimalOfDualEdge_injOn L

/--
[triHexTorus_dual_openCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma triHexTorus_dual_openCount_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (Sym2 (TorusSite L))} :
-- imply
  FK.openCount (hexagonalTorusGraph L) (triHexTorusDualConfig L omega) = (hexagonalTorusGraph L).edgeFinset.card - FK.openCount (triangularTorusGraph L) omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_dual_openCount L omega

/--
[triHexTorus_euler](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma triHexTorus_euler_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (TorusSite L)} :
-- imply
  (Nat.card (TorusSite L) : ℤ) - K.edgeSet.ncard + triHexTorusFaceCount L K = Nat.card K.ConnectedComponent + 1 - triHexTorusDefect L K := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_euler L K

/--
[triHexTorusFaceCount_openSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma triHexTorusFaceCount_openSub_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (Sym2 (TorusSite L))} :
-- imply
  triHexTorusFaceCount L (FK.openSub (triangularTorusGraph L) omega) = FK.numClusters (hexagonalTorusGraph L) (triHexTorusDualConfig L omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusFaceCount_openSub L omega

/--
[triHexTorus_edge_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma triHexTorus_edge_card_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  (triangularTorusGraph L).edgeFinset.card = (hexagonalTorusGraph L).edgeFinset.card := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_edge_card L

/--
[triHexTorus_fkWeight_duality_signed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma triHexTorus_fkWeight_duality_signed_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (Sym2 (TorusSite L))}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.fkWeight (triangularTorusGraph L) p q omega * q ^ ((triangularTorusGraph L).edgeFinset.card + 1) = (p / (1 - BeffaraDC.dualParam p q)) ^ (triangularTorusGraph L).edgeFinset.card * q ^ Nat.card (TorusSite L) * FK.fkWeight (hexagonalTorusGraph L) (BeffaraDC.dualParam p q) q (triHexTorusDualConfig L omega) * q ^ triHexTorusDefect L (FK.openSub (triangularTorusGraph L) omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_fkWeight_duality_signed L omega hp hp1 hq

/--
[triHexTorus_sectorSum_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma triHexTorus_sectorSum_duality_eq
  {L : ℕ}
  [Fact (2 < L)]
  {r : ℤ}
  {F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  triHexTorusPrimalSectorSum L r p q F * q ^ ((triangularTorusGraph L).edgeFinset.card + 1) = (p / (1 - BeffaraDC.dualParam p q)) ^ (triangularTorusGraph L).edgeFinset.card * q ^ Nat.card (TorusSite L) * triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q F * q ^ r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_sectorSum_duality L r F hp hp1 hq

/--
[triHexTorus_sectorPartition_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma triHexTorus_sectorPartition_duality_eq
  {L : ℕ}
  [Fact (2 < L)]
  {r : ℤ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  triHexTorusPrimalSectorSum L r p q (fun _ => 1) * q ^ ((triangularTorusGraph L).edgeFinset.card + 1) = (p / (1 - BeffaraDC.dualParam p q)) ^ (triangularTorusGraph L).edgeFinset.card * q ^ Nat.card (TorusSite L) * triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q (fun _ => 1) * q ^ r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_sectorPartition_duality L r hp hp1 hq

/--
[triHexTorus_sectorNormalized_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean)
-/
@[path]
private lemma triHexTorus_sectorNormalized_duality_eq
  {L : ℕ}
  [Fact (2 < L)]
  {r : ℤ}
  {F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hprimal : triHexTorusPrimalSectorSum L r p q (fun _ => 1) ≠ 0)
  (hdual : triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q (fun _ => 1) ≠ 0) :
-- imply
  triHexTorusPrimalSectorSum L r p q F / triHexTorusPrimalSectorSum L r p q (fun _ => 1) = triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q F / triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q (fun _ => 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_sectorNormalized_duality L r F hp hp1 hq hprimal hdual


-- created on 2026-10-23
