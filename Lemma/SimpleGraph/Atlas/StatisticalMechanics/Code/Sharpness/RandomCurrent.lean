import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
open SimpleGraph Finset StatMech StatMech.Sharpness


/--
[mem_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma mem_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x : V} :
-- imply
  x ∈ sources G n ↔ Odd (incidentFlux G n x) := by
-- proof
  apply StatMech.Sharpness.mem_sources G

/--
[weight_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma weight_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ} :
-- imply
  weight G β J (fun _ => 0) = 1 := by
-- proof
  apply StatMech.Sharpness.weight_zero G β J

/--
[currentSubgraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma currentSubgraph_adj_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V} :
-- imply
  (currentSubgraph G n).Adj x y ↔ G.Adj x y ∧ 1 ≤ n s(x, y) := by
-- proof
  apply StatMech.Sharpness.currentSubgraph_adj G n x y

/--
[currentSubgraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma currentSubgraph_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V} :
-- imply
  currentSubgraph G n ≤ G := by
-- proof
  apply StatMech.Sharpness.currentSubgraph_le G n

/--
[CurrentConnected.refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma refl_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x : V} :
-- imply
  CurrentConnected G n x x := by
-- proof
  apply StatMech.Sharpness.CurrentConnected.refl G n x

/--
[CurrentConnected.symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V}
-- given
  (h : CurrentConnected G n x y) :
-- imply
  CurrentConnected G n y x := by
-- proof
  apply StatMech.Sharpness.CurrentConnected.symm G h

/--
[CurrentConnected.trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma trans_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y z : V}
-- given
  (hxy : CurrentConnected G n x y)
  (hyz : CurrentConnected G n y z) :
-- imply
  CurrentConnected G n x z := by
-- proof
  apply StatMech.Sharpness.CurrentConnected.trans G hxy hyz

/--
[oddSubgraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma oddSubgraph_adj_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V} :
-- imply
  (oddSubgraph G n).Adj x y ↔ G.Adj x y ∧ Odd (n s(x, y)) := by
-- proof
  apply StatMech.Sharpness.oddSubgraph_adj G n x y

/--
[oddSubgraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma oddSubgraph_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V} :
-- imply
  oddSubgraph G n ≤ G := by
-- proof
  apply StatMech.Sharpness.oddSubgraph_le G n

/--
[oddSubgraph_le_currentSubgraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma oddSubgraph_le_currentSubgraph_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V} :
-- imply
  oddSubgraph G n ≤ currentSubgraph G n := by
-- proof
  apply StatMech.Sharpness.oddSubgraph_le_currentSubgraph G n

/--
[backbone_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma backbone_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V}
  [LinearOrder (IsBackbonePath G n x y)]
  {p : IsBackbonePath G n x y}
-- given
  (h : Nonempty (IsBackbonePath G n x y)) :
-- imply
  backbone G n x y h ≤ p := by
-- proof
  apply StatMech.Sharpness.backbone_le G n x y h p

/--
[IsBackbonePath.currentConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma currentConnected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V}
  {p : IsBackbonePath G n x y} :
-- imply
  CurrentConnected G n x y := by
-- proof
  apply StatMech.Sharpness.IsBackbonePath.currentConnected G p

/--
[percolationField_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma percolationField_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {e : Sym2 V} :
-- imply
  percolationField n e = true ↔ 1 ≤ n e := by
-- proof
  apply StatMech.Sharpness.percolationField_apply G n e

/--
[currentSubgraph_eq_percolationField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma currentSubgraph_eq_percolationField_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V} :
-- imply
  currentSubgraph G n = G ⊓ SimpleGraph.fromEdgeSet {e | percolationField n e = true} := by
-- proof
  apply StatMech.Sharpness.currentSubgraph_eq_percolationField G n

/--
[currentConnected_iff_percolationField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma currentConnected_iff_percolationField_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V} :
-- imply
  CurrentConnected G n x y ↔ (G ⊓ SimpleGraph.fromEdgeSet {e | percolationField n e = true}).Reachable x y := by
-- proof
  apply StatMech.Sharpness.currentConnected_iff_percolationField G n x y

/--
[withGhost_adj_some_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma withGhost_adj_some_some_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V} :
-- imply
  (withGhost G).Adj (some x) (some y) ↔ G.Adj x y := by
-- proof
  apply StatMech.Sharpness.withGhost_adj_some_some G x y

/--
[withGhost_adj_some_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma withGhost_adj_some_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V} :
-- imply
  (withGhost G).Adj (some x) ghost := by
-- proof
  apply StatMech.Sharpness.withGhost_adj_some_ghost G x

/--
[withGhost_adj_ghost_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma withGhost_adj_ghost_some_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V} :
-- imply
  (withGhost G).Adj ghost (some x) := by
-- proof
  apply StatMech.Sharpness.withGhost_adj_ghost_some G x

/--
[withGhost_ghost_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma withGhost_ghost_adj_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V} :
-- imply
  (withGhost G).Adj ghost (some x) := by
-- proof
  apply StatMech.Sharpness.withGhost_ghost_adj G x

/--
[withGhost_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean)
-/
@[path]
private lemma withGhost_restrict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V} :
-- imply
  (withGhost G).Adj (some x) (some y) ↔ G.Adj x y := by
-- proof
  apply StatMech.Sharpness.withGhost_restrict G x y


-- created on 2026-10-23
