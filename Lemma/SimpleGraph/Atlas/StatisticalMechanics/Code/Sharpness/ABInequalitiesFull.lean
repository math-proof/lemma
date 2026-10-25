import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.ABInequalitiesFull.Part2
open MeasureTheory Set Finset StatMech StatMech.Sharpness


/--
[sab_inducedWalkTransfer_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalitiesFull.lean)
-/
@[path]
private lemma sab_inducedWalkTransfer_edges_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {ω ω' : ConfigSpace (Sym2 V)}
  {A : Set V}
  {x y : A}
  {w : ((openSub G ω).induce A).Walk x y}
-- given
  (hagree : ∀ e ∈ sab_inducedEdgeSet G ω A w, ω e = ω' e) :
-- imply
  (sab_inducedWalkTransfer G w hagree).edges = w.edges := by
-- proof
  apply StatMech.Sharpness.sab_inducedWalkTransfer_edges G w hagree

/--
[sab_sym2_map_val_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalitiesFull.lean)
-/
@[path]
private lemma sab_sym2_map_val_injective_eq
  [DecidableEq V]
  {A : Set V} :
-- imply
  Function.Injective (Sym2.map (Subtype.val : A → V)) := by
-- proof
  apply StatMech.Sharpness.sab_sym2_map_val_injective

/--
[sab_inducedEdgeSet_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalitiesFull.lean)
-/
@[path]
private lemma sab_inducedEdgeSet_avoid_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {ω : ConfigSpace (Sym2 V)}
  {A : Set V}
  {u a : A}
  {w : ((openSub G ω).induce A).Walk u a}
  {X Y : A}
-- given
  (hav : s(X, Y) ∉ w.edges) :
-- imply
  s((X:V),(Y:V)) ∉ sab_inducedEdgeSet G ω A w := by
-- proof
  apply StatMech.Sharpness.sab_inducedEdgeSet_avoid w hav

/--
[sab_inducedEdgeSet_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalitiesFull.lean)
-/
@[path]
private lemma sab_inducedEdgeSet_disjoint_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {ω : ConfigSpace (Sym2 V)}
  {A : Set V}
  {x y x' y' : A}
  {p : ((openSub G ω).induce A).Walk x y}
  {q : ((openSub G ω).induce A).Walk x' y'}
-- given
  (h : ∀ z, z ∈ p.edges → z ∈ q.edges → False) :
-- imply
  Disjoint (sab_inducedEdgeSet G ω A p) (sab_inducedEdgeSet G ω A q) := by
-- proof
  apply StatMech.Sharpness.sab_inducedEdgeSet_disjoint G ω A p q h

/--
[sab_occursOn_connEvent_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalitiesFull.lean)
-/
@[path]
private lemma sab_occursOn_connEvent_of_walk_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {ω : ConfigSpace (Sym2 V)}
  {A : Set V}
  {u a : V}
  {w : ((openSub G ω).induce A).Walk ⟨u, hu⟩ ⟨a, ha⟩}
-- given
  (hu : u ∈ A)
  (ha : a ∈ A) :
-- imply
  OccursOn (connEvent G A u {a}) (sab_inducedEdgeSet G ω A w) ω := by
-- proof
  apply StatMech.Sharpness.sab_occursOn_connEvent_of_walk G ω A hu ha w

/--
[sab_occursOn_connEventSet_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalitiesFull.lean)
-/
@[path]
private lemma sab_occursOn_connEventSet_of_walk_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {ω : ConfigSpace (Sym2 V)}
  {A : Set V}
  {u b : V}
  {B : Set V}
  {w : ((openSub G ω).induce A).Walk ⟨u, hu⟩ ⟨b, hb⟩}
-- given
  (hu : u ∈ A)
  (hb : b ∈ A)
  (hbB : b ∈ B) :
-- imply
  OccursOn (connEvent G A u B) (sab_inducedEdgeSet G ω A w) ω := by
-- proof
  apply StatMech.Sharpness.sab_occursOn_connEventSet_of_walk G ω A B hu hb hbB w

/--
[sab_setOpen_eq_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalitiesFull.lean)
-/
@[path]
private lemma sab_setOpen_eq_off_eq
  [DecidableEq V]
  {ω : ConfigSpace (Sym2 V)}
  {x y : V}
  {e : Sym2 V}
-- given
  (h : e ≠ s(x,y)) :
-- imply
  setOpen s(x,y) ω e = ω e := by
-- proof
  apply StatMech.Sharpness.sab_setOpen_eq_off h

/--
[sab_setClosed_eq_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalitiesFull.lean)
-/
@[path]
private lemma sab_setClosed_eq_off_eq
  [DecidableEq V]
  {ω : ConfigSpace (Sym2 V)}
  {x y : V}
  {e : Sym2 V}
-- given
  (h : e ≠ s(x,y)) :
-- imply
  setClosed s(x,y) ω e = ω e := by
-- proof
  apply StatMech.Sharpness.sab_setClosed_eq_off h

/--
[sab_transfer_avoid_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalitiesFull.lean)
-/
@[path]
private lemma sab_transfer_avoid_edges_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {ωS ω : ConfigSpace (Sym2 V)}
  {A : Set V}
  {x y : V}
  {u a : A}
  {w : ((openSub G ωS).induce A).Walk u a}
-- given
  (hx : x ∈ A)
  (hy : y ∈ A)
  (hagreeOff : ∀ e, e ≠ s(x,y) → ωS e = ω e)
  (hav : s((⟨x,hx⟩ : A), (⟨y,hy⟩ : A)) ∉ w.edges) :
-- imply
  (sab_transfer_avoid G A x y hx hy hagreeOff w hav).edges = w.edges := by
-- proof
  apply StatMech.Sharpness.sab_transfer_avoid_edges G A x y hx hy hagreeOff w hav

/--
[sab_path_head_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalitiesFull.lean)
-/
@[path]
private lemma sab_path_head_edge_eq
  [DecidableEq V]
  {H : SimpleGraph W}
  {X b Y : W}
  {q : H.Walk X b}
-- given
  (hq : q.support.Nodup)
  (heY : s(X, Y) ∈ q.edges) :
-- imply
  ∃ (h : H.Adj X Y) (r : H.Walk Y b), q = Walk.cons h r ∧ s(X, Y) ∉ r.edges := by
-- proof
  apply StatMech.Sharpness.sab_path_head_edge X b Y q hq heY

/--
[sab_path_split_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalitiesFull.lean)
-/
@[path]
private lemma sab_path_split_edge_eq
  [DecidableEq V]
  {H : SimpleGraph W}
  {u b X Y : W}
  {p : H.Walk u b}
-- given
  (hp : p.IsPath)
  (he : s(X, Y) ∈ p.edges) :
-- imply
  ∃ (p1 p2 : W), (s(p1, p2) = s(X, Y)) ∧ ∃ (q1 : H.Walk u p1) (q2 : H.Walk p2 b), s(X, Y) ∉ q1.edges ∧ s(X, Y) ∉ q2.edges ∧ q1.edges.Disjoint q2.edges ∧ q1.edges ⊆ p.edges ∧ q2.edges ⊆ p.edges := by
-- proof
  apply StatMech.Sharpness.sab_path_split_edge u b X Y p hp he

/--
[sab_pivotal_subset_firstExit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalitiesFull.lean)
-/
@[path]
private lemma sab_pivotal_subset_firstExit_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {A : Set V}
  {u : V}
  {B : Set V}
  {x y : V}
-- given
  (hu : u ∈ A)
  (hx : x ∈ A)
  (hy : y ∈ A) :
-- imply
  {ω | IsPivotal s(x,y) (connEvent G A u B) ω} ⊆ (disjointOccurrence (connEvent G A u {x}) (connEvent G A y B)) ∪ (disjointOccurrence (connEvent G A u {y}) (connEvent G A x B)) := by
-- proof
  apply StatMech.Sharpness.sab_pivotal_subset_firstExit G A u B x y hu hx hy

/--
[sab_pivotal_firstExit_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalitiesFull.lean)
-/
@[path]
private lemma sab_pivotal_firstExit_increasing_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {A : Set V}
  {u : V}
  {B : Set V}
  {x y : V}
-- given
  (hu : u ∈ A)
  (hx : x ∈ A)
  (hy : y ∈ A) :
-- imply
  IsIncreasing (disjointOccurrence (connEvent G A u {x}) (connEvent G A y B)) ∧ IsIncreasing (disjointOccurrence (connEvent G A u {y}) (connEvent G A x B)) ∧ {ω | IsPivotal s(x,y) (connEvent G A u B) ω} ⊆ (disjointOccurrence (connEvent G A u {x}) (connEvent G A y B)) ∪ (disjointOccurrence (connEvent G A u {y}) (connEvent G A x B)) := by
-- proof
  apply StatMech.Sharpness.sab_pivotal_firstExit_increasing G A u B x y hu hx hy


-- created on 2026-10-23
