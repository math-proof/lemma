import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarGraph
open Finset Set SimpleGraph MeasureTheory StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[siteTranslate_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma siteTranslate_apply_eq
  {z x : Site 2} :
-- imply
  siteTranslate z x = x + z := by
-- proof
  apply StatMech.FK.PeriodicPlanar.siteTranslate_apply z x

/--
[PeriodicGraph.mem_orbitBox_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma mem_orbitBox_iff_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ}
  {v : V} :
-- imply
  v ∈ P.orbitBox n ↔ ∃ z : Site 2, z ∈ box 2 n ∧ ∃ u ∈ P.fundamentalDomain, P.shift z u = v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.mem_orbitBox_iff P n v

/--
[PeriodicGraph.orbitBox_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma orbitBox_mono_eq
  [DecidableEq V]
  {P : PeriodicGraph V} :
-- imply
  Monotone P.orbitBox := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.orbitBox_mono P

/--
[PeriodicGraph.mem_orbitBox_of_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma mem_orbitBox_of_eventually_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {v : V} :
-- imply
  ∃ n, v ∈ P.orbitBox n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.mem_orbitBox_of_eventually P v

/--
[PeriodicGraph.edgeIncl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma edgeIncl_injective_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ} :
-- imply
  Function.Injective (P.edgeIncl n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.edgeIncl_injective P n

/--
[PeriodicGraph.extendEdge_edgeIncl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma extendEdge_edgeIncl_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ}
  {omega : ConfigSpace (Sym2 (P.OrbitVertex n))}
  {e : Sym2 (P.OrbitVertex n)} :
-- imply
  P.extendEdge n omega (P.edgeIncl n e) = omega e := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.extendEdge_edgeIncl P n omega e

/--
[PeriodicGraph.monotone_extendEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma monotone_extendEdge_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ} :
-- imply
  Monotone (P.extendEdge n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.monotone_extendEdge P n

/--
[PeriodicGraph.measurable_extendEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma measurable_extendEdge_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ} :
-- imply
  Measurable (P.extendEdge n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.measurable_extendEdge P n

/--
[PeriodicGraph.freeInfiniteVolume_isLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma freeInfiniteVolume_isLimit_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∃ phi : ℕ → ℕ, StrictMono phi ∧ WeakConvergesTo (fun n => P.freeFiniteMeasure (phi n) hp hp1 hq) (P.freeInfiniteVolume hp hp1 hq) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeInfiniteVolume_isLimit P hp hp1 hq

/--
[PeriodicGraph.wiredInfiniteVolume_isLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma wiredInfiniteVolume_isLimit_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∃ phi : ℕ → ℕ, StrictMono phi ∧ WeakConvergesTo (fun n => P.wiredFiniteMeasure (phi n) hp hp1 hq) (P.wiredInfiniteVolume hp hp1 hq) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredInfiniteVolume_isLimit P hp hp1 hq

/--
[triangularStep_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma triangularStep_ne_zero_eq
  [DecidableEq V]
  {i : Fin 3} :
-- imply
  triangularStep i ≠ 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularStep_ne_zero i

/--
[triangularGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma triangularGraph_adj_eq
  [DecidableEq V]
  {x y : Site 2} :
-- imply
  triangularGraph.Adj x y ↔ triangularAdj x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularGraph_adj x y

/--
[triangular_adj_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma triangular_adj_neighbor_eq
  [DecidableEq V]
  {x : Site 2}
  {ib : Fin 3 × Bool} :
-- imply
  triangularGraph.Adj x (triangularNeighbor x ib) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_adj_neighbor x ib

/--
[triangular_mem_candidates_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma triangular_mem_candidates_of_adj_eq
  [DecidableEq V]
  {x y : Site 2}
-- given
  (h : triangularGraph.Adj x y) :
-- imply
  y ∈ Finset.univ.image (triangularNeighbor x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_mem_candidates_of_adj h

/--
[hexagonalGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma hexagonalGraph_adj_eq
  [DecidableEq V]
  {u v : HexVertex} :
-- imply
  hexagonalGraph.Adj u v ↔ hexagonalAdj u v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalGraph_adj u v

/--
[hexagonal_adj_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma hexagonal_adj_neighbor_eq
  [DecidableEq V]
  {u : HexVertex}
  {i : Fin 3} :
-- imply
  hexagonalGraph.Adj u (hexagonalNeighbor u i) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_adj_neighbor u i

/--
[hexagonal_mem_candidates_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma hexagonal_mem_candidates_of_adj_eq
  [DecidableEq V]
  {u v : HexVertex}
-- given
  (h : hexagonalGraph.Adj u v) :
-- imply
  v ∈ Finset.univ.image (hexagonalNeighbor u) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_mem_candidates_of_adj h

/--
[hexTranslate_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean)
-/
@[path]
private lemma hexTranslate_apply_eq
  [DecidableEq V]
  {z : Site 2}
  {u : HexVertex} :
-- imply
  hexTranslate z u = (u.1 + z, u.2) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexTranslate_apply z u


-- created on 2026-10-23
