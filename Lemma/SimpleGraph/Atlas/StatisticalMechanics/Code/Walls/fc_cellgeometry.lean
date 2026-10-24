import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.fc_cellgeometry
open SimpleGraph Filter Topology Set StatMech StatMech.Walls


/--
[fc_fkZEdge_iso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_cellgeometry.lean)
-/
@[path]
private lemma fc_fkZEdge_iso_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {φ : G ≃g H}
  {p q : ℝ} :
-- imply
  ecz_fkZEdge G p q = ecz_fkZEdge H p q := by
-- proof
  apply StatMech.Walls.fc_fkZEdge_iso φ p q

/--
[fc_vanHoveTag_eq_some_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_cellgeometry.lean)
-/
@[path]
private lemma fc_vanHoveTag_eq_some_iff_eq
  {d : ℕ}
  {m n : ℕ}
  {x : boxVerts d n}
  {c : Fin d → Fin (fc_Tcg m n)} :
-- imply
  fc_vanHoveTag m n x = some c ↔ ∀ i, ((x : Site d) i - fc_center m n c i).natAbs ≤ m := by
-- proof
  apply StatMech.Walls.fc_vanHoveTag_eq_some_iff m n x c

/--
[fc_cellBlockIso_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_cellgeometry.lean)
-/
@[path]
private lemma fc_cellBlockIso_apply_eq
  {d : ℕ}
  {m n : ℕ}
  {c : Fin d → Fin (fc_Tcg m n)}
  {y : boxVerts d m} :
-- imply
  (((fc_cellBlockIso m n c y : {x : boxVerts d n // fc_vanHoveTag m n x = some c}) : boxVerts d n) : Site d) = fun i => (y : Site d) i + fc_center m n c i := by
-- proof
  apply StatMech.Walls.fc_cellBlockIso_apply m n c y

/--
[fc_cellBlock_fkZEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_cellgeometry.lean)
-/
@[path]
private lemma fc_cellBlock_fkZEdge_eq
  {d : ℕ}
  {m n : ℕ}
  {c : Fin d → Fin (fc_Tcg m n)}
  {p q : ℝ} :
-- imply
  ecz_fkZEdge (qp_blkG (boxGraph d n) (fc_vanHoveTag m n) (some c)) p q = ecz_fkZEdge (boxGraph d m) p q := by
-- proof
  apply StatMech.Walls.fc_cellBlock_fkZEdge m n c p q

/--
[fc_cellBlock_fkZEdge_via_iso_load_bearing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_cellgeometry.lean)
-/
@[path]
private lemma fc_cellBlock_fkZEdge_via_iso_load_bearing_eq
  {d : ℕ}
  {m n : ℕ}
  {c : Fin d → Fin (fc_Tcg m n)}
  {p q : ℝ} :
-- imply
  ecz_fkZEdge (qp_blkG (boxGraph d n) (fc_vanHoveTag m n) (some c)) p q = ecz_fkZEdge (boxGraph d m) p q := by
-- proof
  apply StatMech.Walls.fc_cellBlock_fkZEdge_via_iso_load_bearing m n c p q

/--
[fc_cellBlock_edge_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_cellgeometry.lean)
-/
@[path]
private lemma fc_cellBlock_edge_card_eq
  {d : ℕ}
  {m n : ℕ}
  {c : Fin d → Fin (fc_Tcg m n)} :
-- imply
  (qp_blkG (boxGraph d n) (fc_vanHoveTag m n) (some c)).edgeFinset.card = (boxGraph d m).edgeFinset.card := by
-- proof
  apply StatMech.Walls.fc_cellBlock_edge_card m n c

/--
[fc_cell_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_cellgeometry.lean)
-/
@[path]
private lemma fc_cell_card_eq
  {d : ℕ}
  {m n : ℕ} :
-- imply
  Fintype.card (Fin d → Fin (fc_Tcg m n)) = (fc_Tcg m n) ^ d := by
-- proof
  apply StatMech.Walls.fc_cell_card m n

/--
[fc_cellBlockIso_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_cellgeometry.lean)
-/
@[path]
private lemma fc_cellBlockIso_nonvacuous_eq
  {d : ℕ}
  {m n : ℕ}
-- given
  (hmn : m ≤ n) :
-- imply
  ∃ c : Fin d → Fin (fc_Tcg m n), Nonempty (boxGraph d m ≃g qp_blkG (boxGraph d n) (fc_vanHoveTag m n) (some c)) := by
-- proof
  apply StatMech.Walls.fc_cellBlockIso_nonvacuous m n hmn


-- created on 2026-10-23
