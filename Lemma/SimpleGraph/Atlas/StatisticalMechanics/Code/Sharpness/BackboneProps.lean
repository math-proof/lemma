import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
open SimpleGraph Finset StatMech StatMech.Sharpness


/--
[walkDeg_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneProps.lean)
-/
@[path]
private lemma walkDeg_nil_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph V}
  {a : V}
  {x : V} :
-- imply
  walkDeg (Walk.nil : H.Walk a a) x = 0 := by
-- proof
  apply StatMech.Sharpness.walkDeg_nil G x

/--
[walkDeg_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneProps.lean)
-/
@[path]
private lemma walkDeg_cons_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph V}
  {u v w : V}
  {p : H.Walk v w}
  {x : V}
-- given
  (h : H.Adj u v) :
-- imply
  walkDeg (Walk.cons h p) x = (if x ∈ (s(u, v) : Sym2 V) then 1 else 0) + walkDeg p x := by
-- proof
  apply StatMech.Sharpness.walkDeg_cons G h p x

/--
[walkDeg_eq_zero_of_not_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneProps.lean)
-/
@[path]
private lemma walkDeg_eq_zero_of_not_support_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph V}
  {a b : V}
  {p : H.Walk a b}
  {x : V}
-- given
  (hx : x ∉ p.support) :
-- imply
  walkDeg p x = 0 := by
-- proof
  apply StatMech.Sharpness.walkDeg_eq_zero_of_not_support G p x hx

/--
[walkDeg_odd_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneProps.lean)
-/
@[path]
private lemma walkDeg_odd_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph V}
  {a b : V}
  {p : H.Walk a b}
  {x : V}
-- given
  (hp : p.IsPath) :
-- imply
  Odd (walkDeg p x) ↔ (x = a ∨ x = b) ∧ a ≠ b := by
-- proof
  apply StatMech.Sharpness.walkDeg_odd_iff G p hp x

/--
[sum_count_eq_walkDeg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneProps.lean)
-/
@[path]
private lemma sum_count_eq_walkDeg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph V}
  {a b : V}
  {p : H.Walk a b}
  {x : V}
-- given
  (hsub : ∀ e ∈ p.edges, e ∈ G.edgeFinset) :
-- imply
  ∑ e ∈ G.edgeFinset.filter (fun e => x ∈ e), (p.edges).count e = walkDeg p x := by
-- proof
  apply StatMech.Sharpness.sum_count_eq_walkDeg G p x hsub

/--
[isBackbonePath_edge_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneProps.lean)
-/
@[path]
private lemma isBackbonePath_edge_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph V}
  {n : Current V}
  {a b : V}
  {p : IsBackbonePath G n a b}
  {e : Sym2 V}
-- given
  (he : e ∈ p.1.edges) :
-- imply
  Odd (n e) := by
-- proof
  apply StatMech.Sharpness.isBackbonePath_edge_odd G p he

/--
[isBackbonePath_edge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneProps.lean)
-/
@[path]
private lemma isBackbonePath_edge_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph V}
  {n : Current V}
  {a b : V}
  {p : IsBackbonePath G n a b}
  {e : Sym2 V}
-- given
  (he : e ∈ p.1.edges) :
-- imply
  e ∈ G.edgeFinset := by
-- proof
  apply StatMech.Sharpness.isBackbonePath_edge_mem G p he

/--
[isBackbonePath_edge_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneProps.lean)
-/
@[path]
private lemma isBackbonePath_edge_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph V}
  {n : Current V}
  {a b : V}
  {p : IsBackbonePath G n a b}
  {e : Sym2 V}
-- given
  (he : e ∈ p.1.edges) :
-- imply
  1 ≤ n e := by
-- proof
  apply StatMech.Sharpness.isBackbonePath_edge_pos G p he

/--
[isBackbonePath_currentConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneProps.lean)
-/
@[path]
private lemma isBackbonePath_currentConnected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph V}
  {n : Current V}
  {a b : V}
  {p : IsBackbonePath G n a b} :
-- imply
  CurrentConnected G n a b := by
-- proof
  apply StatMech.Sharpness.isBackbonePath_currentConnected G p

/--
[backbone_currentConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneProps.lean)
-/
@[path]
private lemma backbone_currentConnected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph V}
  {n : Current V}
  {a b : V}
  [LinearOrder (IsBackbonePath G n a b)]
-- given
  (h : Nonempty (IsBackbonePath G n a b)) :
-- imply
  CurrentConnected G n a b := by
-- proof
  apply StatMech.Sharpness.backbone_currentConnected G n a b h

/--
[backbone_edge_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneProps.lean)
-/
@[path]
private lemma backbone_edge_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph V}
  {n : Current V}
  {a b : V}
  [LinearOrder (IsBackbonePath G n a b)]
  {e : Sym2 V}
-- given
  (h : Nonempty (IsBackbonePath G n a b))
  (he : e ∈ (backbone G n a b h).1.edges) :
-- imply
  Odd (n e) := by
-- proof
  apply StatMech.Sharpness.backbone_edge_odd G n a b h he

/--
[removeWalk_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneProps.lean)
-/
@[path]
private lemma removeWalk_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph V}
  {a b : V}
  {n : Current V}
  {p : H.Walk a b}
  {e : Sym2 V} :
-- imply
  removeWalk n p e = n e - p.edges.count e := by
-- proof
  apply StatMech.Sharpness.removeWalk_apply G n p e

/--
[incidentFlux_removeWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneProps.lean)
-/
@[path]
private lemma incidentFlux_removeWalk_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph V}
  {a b : V}
  {n : Current V}
  {p : H.Walk a b}
  {x : V}
-- given
  (hsub : ∀ e ∈ p.edges, e ∈ G.edgeFinset)
  (hle : ∀ e ∈ G.edgeFinset, p.edges.count e ≤ n e) :
-- imply
  incidentFlux G (removeWalk n p) x = incidentFlux G n x - walkDeg p x := by
-- proof
  apply StatMech.Sharpness.incidentFlux_removeWalk G n p hsub hle x

/--
[sources_removeWalk_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneProps.lean)
-/
@[path]
private lemma sources_removeWalk_eq_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph V}
  {n : Current V}
  {a b : V}
  {p : IsBackbonePath G n a b}
-- given
  (hab : a ≠ b)
  (hsrc : sources G n = {a, b}) :
-- imply
  sources G (removeWalk n p.1) = ∅ := by
-- proof
  apply StatMech.Sharpness.sources_removeWalk_eq_empty G p hab hsrc


-- created on 2026-10-23
