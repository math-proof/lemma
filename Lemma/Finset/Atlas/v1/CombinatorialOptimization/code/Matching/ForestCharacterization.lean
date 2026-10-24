import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.CombinatorialOptimization.code.Matching.ForestCharacterization
open SimpleGraph


namespace SimpleGraph

/--
[Walk.IsAugmentingPath.odd_length](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/ForestCharacterization.lean)
-/
@[path]
lemma Walk.IsAugmentingPath.odd_length
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
  {M : G.Subgraph}
-- given
  (haug : p.IsAugmentingPath M) :
-- imply
  Odd p.edges.length := by
-- proof
  obtain ⟨_, huv, _, hv, halt⟩ := haug
  have hpos : 0 < p.edges.length := by
    by_contra h; push_neg at h
    exact huv (p.eq_of_length_eq_zero (by rw [← p.length_edges]; omega))
  by_contra hnodd
  rw [Nat.not_odd_iff_even] at hnodd
  have hlast_idx : p.edges.length - 1 < p.edges.length := Nat.sub_lt hpos Nat.one_pos
  have hlast_odd : Odd (p.edges.length - 1) := by
    obtain ⟨k, hk⟩ := hnodd; cases k with
    | zero => omega
    | succ j => exact ⟨j, by omega⟩
  have hlast_in_M := (halt (p.edges.length - 1) hlast_idx).2 hlast_odd
  have hedge := Walk.edges_getElem_eq p (p.edges.length - 1) hlast_idx
  rw [hedge] at hlast_in_M
  have hlen_eq : p.edges.length = p.length := p.length_edges
  have hidx : p.edges.length - 1 + 1 = p.length := by omega
  rw [hidx, p.getVert_length] at hlast_in_M
  rw [Subgraph.mem_edgeSet] at hlast_in_M
  exact hv (M.edge_vert hlast_in_M.symm)

end SimpleGraph

namespace SimpleGraph

/--
[Walk.IsAlternatingFrom.reverse_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/ForestCharacterization.lean)
-/
@[path]
lemma Walk.IsAlternatingFrom.reverse_of_odd
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
  {M : G.Subgraph}
-- given
  (halt : p.IsAlternatingFrom M)
  (hodd : Odd p.edges.length) :
-- imply
  p.reverse.IsAlternatingFrom M := by
-- proof
  have hlen_eq : p.reverse.edges.length = p.edges.length := by
    rw [Walk.edges_reverse, List.length_reverse]
  intro i hi
  have hi' : i < p.edges.length := by omega
  have hget : p.reverse.edges[i]'hi = p.edges[p.edges.length - 1 - i]'(by omega) := by
    have h1 : p.reverse.edges = p.edges.reverse := Walk.edges_reverse p
    simp only [h1, List.getElem_reverse]
  constructor
  · intro heven
    rw [hget]
    have hkey : Even (p.edges.length - 1 - i) := by
      obtain ⟨k, hk⟩ := hodd; obtain ⟨j, hj⟩ := heven
      exact ⟨k - j, by omega⟩
    exact (halt _ (by omega)).1 hkey
  · intro hodd_i
    rw [hget]
    have hkey : Odd (p.edges.length - 1 - i) := by
      obtain ⟨k, hk⟩ := hodd; obtain ⟨j, hj⟩ := hodd_i
      exact ⟨k - j - 1, by omega⟩
    exact (halt _ (by omega)).2 hkey

end SimpleGraph

namespace SimpleGraph

/--
[Walk.IsAugmentingPath.reverse'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/ForestCharacterization.lean)
-/
@[path]
lemma Walk.IsAugmentingPath.reverse'
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
  {M : G.Subgraph}
-- given
  (haug : p.IsAugmentingPath M) :
-- imply
  p.reverse.IsAugmentingPath M :=
-- proof
  ⟨haug.1.reverse, haug.2.1.symm, haug.2.2.2.1, haug.2.2.1,
    haug.2.2.2.2.reverse_of_odd haug.odd_length⟩

end SimpleGraph

namespace SimpleGraph

/--
[walk_endpoint_parity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/ForestCharacterization.lean)
-/
@[path]
lemma walk_endpoint_parity
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Set V}
  {u v : V}
  {p : G.Walk u v}
-- given
  (hbip : G.IsBipartiteWith A B) :
-- imply
  (u ∈ A → ((Even p.edges.length → v ∈ A) ∧ (Odd p.edges.length → v ∈ B))) ∧ (u ∈ B → ((Even p.edges.length → v ∈ B) ∧ (Odd p.edges.length → v ∈ A))) := by
-- proof
  induction p with
  | nil =>
    exact ⟨fun hu => ⟨fun _ => hu, fun h => absurd h Nat.not_odd_zero⟩,
      fun hu => ⟨fun _ => hu, fun h => absurd h Nat.not_odd_zero⟩⟩
  | @cons u w v hadj q ih =>
    constructor
    · intro hu
      have hw : w ∈ B := hbip.mem_of_mem_adj hu hadj
      have ihB := ih.2 hw
      simp only [Walk.edges_cons, List.length_cons]
      exact ⟨fun heven => ihB.2 (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp heven)),
        fun hodd => ihB.1 (Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hodd))⟩
    · intro hu
      have hw : w ∈ A := hbip.symm.mem_of_mem_adj hu hadj
      have ihA := ih.1 hw
      simp only [Walk.edges_cons, List.length_cons]
      exact ⟨fun heven => ihA.2 (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp heven)),
        fun hodd => ihA.1 (Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hodd))⟩

end SimpleGraph

namespace SimpleGraph

/--
[augmenting_to_forest](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/ForestCharacterization.lean)
-/
@[path]
lemma augmenting_to_forest
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Set V}
  {M : G.Subgraph}
-- given
  (hbip : G.IsBipartiteWith A B)
  (haug : HasAugmentingPath G M) :
-- imply
  ∃ b ∈ B, b ∉ M.verts ∧ IsInAlternatingForest G M A b := by
-- proof
  obtain ⟨u, v, p, hpath, huv, hu, hv, halt⟩ := haug
  have hpos : 0 < p.length := by
    by_contra h; push_neg at h
    exact huv (p.eq_of_length_eq_zero (Nat.eq_zero_of_le_zero h))
  have hadj_u : ∃ w, G.Adj u w := by
    match p with
    | .nil => simp [Walk.length] at hpos
    | .cons hadj _ => exact ⟨_, hadj⟩
  obtain ⟨w, hw⟩ := hadj_u
  have huAB := hbip.mem_of_adj hw
  have haug' : p.IsAugmentingPath M := ⟨hpath, huv, hu, hv, halt⟩
  have hodd : Odd p.edges.length := haug'.odd_length
  obtain ⟨huA, _⟩ | ⟨huB, _⟩ := huAB
  ·
    have hvB : v ∈ B := (walk_endpoint_parity hbip p).1 huA |>.2 hodd
    exact ⟨v, hvB, hv, u, p, huA, hu, hpath, halt⟩
  ·
    have hvA : v ∈ A := (walk_endpoint_parity hbip p).2 huB |>.2 hodd
    exact ⟨u, huB, hu, v, p.reverse, hvA, hv, hpath.reverse, halt.reverse_of_odd hodd⟩

end SimpleGraph

namespace SimpleGraph

/--
[forest_to_augmenting](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/ForestCharacterization.lean)
-/
@[path]
lemma forest_to_augmenting
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Set V}
  {M : G.Subgraph}
  {b : V}
-- given
  (hbip : G.IsBipartiteWith A B)
  (hb : b ∈ B)
  (hbM : b ∉ M.verts)
  (hforest : IsInAlternatingForest G M A b) :
-- imply
  HasAugmentingPath G M := by
-- proof
  obtain ⟨a, p, haA, haM, hpath, halt⟩ := hforest
  have hab : a ≠ b := by
    intro heq; subst heq
    exact Set.disjoint_left.mp hbip.disjoint haA hb
  exact ⟨a, b, p, hpath, hab, haM, hbM, halt⟩

end SimpleGraph

namespace SimpleGraph

/--
[forest_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/ForestCharacterization.lean)
-/
@[path]
lemma forest_characterization
  [DecidableEq V]
  {G : SimpleGraph V}
  {M : G.Subgraph}
  {A B : Set V}
-- given
  (hM : M.IsMatching)
  (hMfin : M.edgeSet.Finite)
  (hbip : G.IsBipartiteWith A B) :
-- imply
  M.IsMaxMatching ↔ ∀ b ∈ B, b ∉ M.verts → ¬ IsInAlternatingForest G M A b := by
-- proof
  rw [berge_lemma M hM hMfin]
  constructor
  ·
    intro hnoaug b hb hbM hforest
    exact hnoaug (forest_to_augmenting hbip hb hbM hforest)
  ·
    intro hnoforest haug
    obtain ⟨b, hb, hbM, hforest⟩ := augmenting_to_forest hbip haug
    exact hnoforest b hb hbM hforest

end SimpleGraph


-- created on 2026-10-23
