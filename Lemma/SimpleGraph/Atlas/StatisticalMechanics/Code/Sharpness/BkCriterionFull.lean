import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
open MeasureTheory Finset StatMech StatMech.Sharpness


/--
[shk_edges_subset_openSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionFull.lean)
-/
@[path]
private lemma shk_edges_subset_openSub_eq
  {G : SimpleGraph V}
  {ω ω' : ConfigSpace (Sym2 V)}
  {u x : V}
  {p : (openSub G ω).Walk u x}
-- given
  (hagree : agreeOn {e : Sym2 V | e ∈ p.edges} ω ω') :
-- imply
  ∀ e ∈ p.edges, e ∈ (openSub G ω').edgeSet := by
-- proof
  apply StatMech.Sharpness.shk_edges_subset_openSub G ω ω' p hagree

/--
[shk_occursOn_connEvent_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionFull.lean)
-/
@[path]
private lemma shk_occursOn_connEvent_of_walk_eq
  {G : SimpleGraph V}
  {ω : ConfigSpace (Sym2 V)}
  {S : Set V}
  {u x : V}
  {p : (openSub G ω).Walk u x}
-- given
  (huS : u ∈ S)
  (hxS : x ∈ S)
  (hsupp : ∀ z ∈ p.support, z ∈ S) :
-- imply
  OccursOn (connEvent G S u {x}) {e : Sym2 V | e ∈ p.edges} ω := by
-- proof
  apply StatMech.Sharpness.shk_occursOn_connEvent_of_walk G ω S u x huS hxS p hsupp

/--
[shk_occursOn_connToSet_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionFull.lean)
-/
@[path]
private lemma shk_occursOn_connToSet_of_walk_eq
  {G : SimpleGraph V}
  {ω : ConfigSpace (Sym2 V)}
  {A : Set V}
  {y b : V}
  {B : Set V}
  {p : (openSub G ω).Walk y b}
-- given
  (hyA : y ∈ A)
  (hbA : b ∈ A)
  (hbB : b ∈ B)
  (hsupp : ∀ z ∈ p.support, z ∈ A) :
-- imply
  OccursOn (connEvent G A y B) {e : Sym2 V | e ∈ p.edges} ω := by
-- proof
  apply StatMech.Sharpness.shk_occursOn_connToSet_of_walk G ω A y b B hyA hbA hbB p hsupp

/--
[shk_occursOn_edgeOpenEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionFull.lean)
-/
@[path]
private lemma shk_occursOn_edgeOpenEvent_eq
  {x y : V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hopen : ω s(x, y) = true) :
-- imply
  OccursOn (edgeOpenEvent x y) {s(x, y)} ω := by
-- proof
  apply StatMech.Sharpness.shk_occursOn_edgeOpenEvent x y ω hopen

/--
[shk_edge_getElem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionFull.lean)
-/
@[path]
private lemma shk_edge_getElem_eq
  {G : SimpleGraph V}
  {a b : V}
  {p : G.Walk a b}
  {i : ℕ}
-- given
  (h : i < p.length) :
-- imply
  p.edges[i]'(by rw [SimpleGraph.Walk.length_edges]; exact h) = s(p.getVert i, p.getVert (i + 1)) := by
-- proof
  apply StatMech.Sharpness.shk_edge_getElem p i h

/--
[shk_walk_of_connToSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionFull.lean)
-/
@[path]
private lemma shk_walk_of_connToSet_eq
  {G : SimpleGraph V}
  {ω : ConfigSpace (Sym2 V)}
  {A : Set V}
  {u : V}
  {B : Set V}
-- given
  (h : ConnToSet G ω A u B) :
-- imply
  ∃ (b : V) (_ : b ∈ A) (_ : b ∈ B) (p : (openSub G ω).Walk u b), ∀ z ∈ p.support, z ∈ A := by
-- proof
  apply StatMech.Sharpness.shk_walk_of_connToSet G ω A u B h

/--
[shk_occursOn_congr_config](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionFull.lean)
-/
@[path]
private lemma shk_occursOn_congr_config_eq
  {A : Set (ConfigSpace V)}
  {K : Set V}
  {ω ω' : ConfigSpace V}
-- given
  (h : OccursOn A K ω)
  (hagree : agreeOn K ω ω') :
-- imply
  OccursOn A K ω' := by
-- proof
  apply StatMech.Sharpness.shk_occursOn_congr_config h hagree

/--
[shk_occursOn_disjointOccurrence_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionFull.lean)
-/
@[path]
private lemma shk_occursOn_disjointOccurrence_union_eq
  {A B : Set (ConfigSpace V)}
  {K L : Set V}
  {ω : ConfigSpace V}
-- given
  (hKL : Disjoint K L)
  (hA : OccursOn A K ω)
  (hB : OccursOn B L ω) :
-- imply
  OccursOn (disjointOccurrence A B) (K ∪ L) ω := by
-- proof
  apply StatMech.Sharpness.shk_occursOn_disjointOccurrence_union hKL hA hB

/--
[shk_firstExit_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionFull.lean)
-/
@[path]
private lemma shk_firstExit_triple_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {ω : ConfigSpace (Sym2 V)}
  {A S B : Set V}
  {u b : V}
  {p : (openSub G ω).Walk u b}
-- given
  (huS : u ∈ S)
  (hbB : b ∈ B)
  (hbS : b ∉ S)
  (hpath : p.IsPath)
  (hsuppA : ∀ z ∈ p.support, z ∈ A) :
-- imply
  ∃ x y : V, x ∈ S ∧ y ∉ S ∧ G.Adj x y ∧ ω ∈ disjointOccurrence (connEvent G S u {x}) (disjointOccurrence (edgeOpenEvent x y) (connEvent G A y B)) := by
-- proof
  apply StatMech.Sharpness.shk_firstExit_triple G ω A S B u b huS hbB hbS p hpath hsuppA

/--
[shk_mem_boundaryPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionFull.lean)
-/
@[path]
private lemma shk_mem_boundaryPairs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Finset V}
  [DecidableRel G.Adj]
  {q : V × V} :
-- imply
  q ∈ shk_boundaryPairs G S ↔ q.1 ∈ S ∧ q.2 ∉ S ∧ G.Adj q.1 q.2 := by
-- proof
  apply StatMech.Sharpness.shk_mem_boundaryPairs G S

/--
[shk_firstExit_inclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionFull.lean)
-/
@[path]
private lemma shk_firstExit_inclusion_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Set V}
  {S : Finset V}
  {B : Set V}
  {u : V}
-- given
  (huS : u ∈ S)
  (hBS : ∀ z ∈ B, z ∉ S) :
-- imply
  connEvent G A u B ⊆ ⋃ q ∈ shk_boundaryPairs G S, disjointOccurrence (connEvent G (S : Set V) u {q.1}) (disjointOccurrence (edgeOpenEvent q.1 q.2) (connEvent G A q.2 B)) := by
-- proof
  apply StatMech.Sharpness.shk_firstExit_inclusion G A S B u huS hBS


-- created on 2026-10-23
