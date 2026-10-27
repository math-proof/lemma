import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc_bdedgecompl
open Finset Set SimpleGraph StatMech StatMech.Walls


/--
[bdEdge_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_bdedgecompl.lean)
-/
@[path]
private lemma bdEdge_compl_eq
  {S : Set (Site 2)}
  {e : Sym2 (Site 2)} :
-- imply
  bdEdge S e ↔ bdEdge Sᶜ e := by
-- proof
  apply StatMech.Walls.bdEdge_compl S e

/--
[bdEdge_compl_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_bdedgecompl.lean)
-/
@[path]
private lemma bdEdge_compl_mk_eq
  {S : Set (Site 2)}
  {x y : Site 2} :
-- imply
  bdEdge S s(x, y) ↔ bdEdge Sᶜ s(x, y) := by
-- proof
  apply StatMech.Walls.bdEdge_compl_mk S x y

/--
[bdEdge_compl_mk_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_bdedgecompl.lean)
-/
@[path]
private lemma bdEdge_compl_mk_iff_eq
  {S : Set (Site 2)}
  {x y : Site 2} :
-- imply
  bdEdge Sᶜ s(x, y) ↔ (x ∉ S ↔ y ∈ S) := by
-- proof
  apply StatMech.Walls.bdEdge_compl_mk_iff S x y

/--
[bdEdgeSet2_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_bdedgecompl.lean)
-/
@[path]
private lemma bdEdgeSet2_compl_eq
  {S : Set (Site 2)} :
-- imply
  bdEdgeSet2 S = bdEdgeSet2 Sᶜ := by
-- proof
  apply StatMech.Walls.bdEdgeSet2_compl S

/--
[faceBoundaryGraph_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_bdedgecompl.lean)
-/
@[path]
private lemma faceBoundaryGraph_compl_eq
  {S : Set (Site 2)} :
-- imply
  faceBoundaryGraph S = faceBoundaryGraph Sᶜ := by
-- proof
  apply StatMech.Walls.faceBoundaryGraph_compl S

/--
[bdEdge_match_compl_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_bdedgecompl.lean)
-/
@[path]
private lemma bdEdge_match_compl_left_eq
  {K T : Set (Site 2)}
-- given
  (hmatch : ∀ e : Sym2 (Site 2), bdEdge K e ↔ bdEdge T e) :
-- imply
  ∀ e : Sym2 (Site 2), bdEdge Kᶜ e ↔ bdEdge T e := by
-- proof
  apply StatMech.Walls.bdEdge_match_compl_left hmatch

/--
[bdEdge_match_compl_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_bdedgecompl.lean)
-/
@[path]
private lemma bdEdge_match_compl_right_eq
  {K T : Set (Site 2)}
-- given
  (hmatch : ∀ e : Sym2 (Site 2), bdEdge K e ↔ bdEdge T e) :
-- imply
  ∀ e : Sym2 (Site 2), bdEdge K e ↔ bdEdge Tᶜ e := by
-- proof
  apply StatMech.Walls.bdEdge_match_compl_right hmatch

/--
[bdEdge_match_compl_both](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_bdedgecompl.lean)
-/
@[path]
private lemma bdEdge_match_compl_both_eq
  {K T : Set (Site 2)} :
-- imply
  (∀ e : Sym2 (Site 2), bdEdge K e ↔ bdEdge T e) ↔ (∀ e : Sym2 (Site 2), bdEdge Kᶜ e ↔ bdEdge Tᶜ e) := by
-- proof
  apply StatMech.Walls.bdEdge_match_compl_both


-- created on 2026-10-23
