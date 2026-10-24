import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc62twin
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc62_residual_gDegGe3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_residual_gDegGe3_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (hog : o ≠ g)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hne1 : degK ends (univ : Finset ι) g ≠ 1) :
-- imply
  3 ≤ degK ends (univ : Finset ι) g := by
-- proof
  apply StatMech.Walls.gc62_residual_gDegGe3 ends hog hxg hyg huniv hne1

/--
[gc62_refut_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_refut_univ_sources_eq :
-- imply
  sources gc62_refutEnds (univ : Finset (Fin 7)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc62_refut_univ_sources

/--
[gc62_refut_K_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_refut_K_sources_eq :
-- imply
  sources gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) = ({0, 1} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc62_refut_K_sources

/--
[gc62_refut_gDeg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_refut_gDeg_eq :
-- imply
  degK gc62_refutEnds (univ : Finset (Fin 7)) (3 : Fin 4) = 3 := by
-- proof
  apply StatMech.Walls.gc62_refut_gDeg

/--
[gc62_refut_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_refut_loopless_eq :
-- imply
  ∀ i : Fin 7, ¬ (gc62_refutEnds i).IsDiag := by
-- proof
  apply StatMech.Walls.gc62_refut_loopless

/--
[gc62_conn_12](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_conn_12_eq :
-- imply
  connK gc62_refutEnds (({0, 5, 6} : Finset (Fin 7)) ∪ ({1, 2} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc62_conn_12

/--
[gc62_conn_13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_conn_13_eq :
-- imply
  connK gc62_refutEnds (({0, 5, 6} : Finset (Fin 7)) ∪ ({1, 3} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc62_conn_13

/--
[gc62_conn_23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_conn_23_eq :
-- imply
  connK gc62_refutEnds (({0, 5, 6} : Finset (Fin 7)) ∪ ({2, 3} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc62_conn_23

/--
[gc62_not_conn_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_not_conn_empty_eq :
-- imply
  ¬ connK gc62_refutEnds (({0, 5, 6} : Finset (Fin 7)) ∪ (∅ : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc62_not_conn_empty

/--
[gc62_refut_LblockSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_refut_LblockSet_eq :
-- imply
  gc51_LblockSet gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 1 3 = ({{1, 2}, {1, 3}, {2, 3}} : Finset (Finset (Fin 7))) := by
-- proof
  apply StatMech.Walls.gc62_refut_LblockSet

/--
[gc62_gIncident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_gIncident_eq
  {i : Fin 7}
  {v : Fin 4}
-- given
  (hi : gc62_refutEnds i = s(v, 3))
  (hv : v ≠ 3) :
-- imply
  i = 4 ∨ i = 5 ∨ i = 6 := by
-- proof
  apply StatMech.Walls.gc62_gIncident i v hi hv

/--
[gc62_parallelTwinPresent_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_parallelTwinPresent_false_eq :
-- imply
  ¬ gc61_ParallelTwinPresent gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc62_parallelTwinPresent_false

/--
[gc62_refut_not_gateInK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_refut_not_gateInK_eq :
-- imply
  ¬ connK gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 1 3 := by
-- proof
  apply StatMech.Walls.gc62_refut_not_gateInK

/--
[gc62_refut_not_gDegOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_refut_not_gDegOne_eq :
-- imply
  degK gc62_refutEnds (univ : Finset (Fin 7)) (3 : Fin 4) ≠ 1 := by
-- proof
  apply StatMech.Walls.gc62_refut_not_gDegOne

/--
[gc62_refut_no_ygEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_refut_no_ygEdge_eq :
-- imply
  ¬ ∃ i, i ∈ (univ : Finset (Fin 7)) \ ({0, 5, 6} : Finset (Fin 7)) ∧ gc62_refutEnds i = s(2, 3) := by
-- proof
  apply StatMech.Walls.gc62_refut_no_ygEdge

/--
[gc62_refut_in_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_refut_in_residual_eq :
-- imply
  3 ≤ degK gc62_refutEnds (univ : Finset (Fin 7)) (3 : Fin 4) := by
-- proof
  apply StatMech.Walls.gc62_refut_in_residual

/--
[gc62_refut_D_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_refut_D_sources_eq :
-- imply
  sources gc62_refutEnds ({1, 4} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc62_refut_D_sources

/--
[gc62_reconn_12](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_reconn_12_eq :
-- imply
  connK gc62_refutEnds ((({0, 5, 6} : Finset (Fin 7)) ∪ ({1, 2} : Finset (Fin 7))) \ {1}) 1 2 := by
-- proof
  apply StatMech.Walls.gc62_reconn_12

/--
[gc62_reconn_13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_reconn_13_eq :
-- imply
  connK gc62_refutEnds ((({0, 5, 6} : Finset (Fin 7)) ∪ ({1, 3} : Finset (Fin 7))) \ {1}) 1 2 := by
-- proof
  apply StatMech.Walls.gc62_reconn_13

/--
[gc62_refut_rerouteConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_refut_rerouteConnector_eq :
-- imply
  gc59_RerouteConnector gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc62_refut_rerouteConnector

/--
[gc62_refut_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_refut_disjointConnector_eq :
-- imply
  gc57_DisjointConnector gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc62_refut_disjointConnector

/--
[gc62_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc62twin.lean)
-/
@[path]
private lemma gc62_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (o x y g : W), o ≠ g → x ≠ g → y ≠ g → sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) → degK ends (univ : Finset ι) g ≠ 1 → 3 ≤ degK ends (univ : Finset ι) g) ∧ (¬ gc61_ParallelTwinPresent gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 1 2 3) ∧ (3 ≤ degK gc62_refutEnds (univ : Finset (Fin 7)) (3 : Fin 4) ∧ ¬ connK gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 1 3 ∧ ¬ ∃ i, i ∈ (univ : Finset (Fin 7)) \ ({0, 5, 6} : Finset (Fin 7)) ∧ gc62_refutEnds i = s(2, 3)) ∧ gc57_DisjointConnector gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc62_status


-- created on 2026-10-23
