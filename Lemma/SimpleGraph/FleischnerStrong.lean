import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part23
open scoped BigOperators
open SimpleGraph


namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[ncard_support_eq_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma IsCycle.ncard_support_eq_length [Finite V] {c : G.Walk x x}
  (hc : c.IsCycle) : {v | v ∈ c.support}.ncard = c.length := by
  classical
  let _ := Fintype.ofFinite V
  have hnil := hc.not_nil
  have htail_support : c.tail.support = c.support.tail :=
    c.support_tail_of_not_nil hnil
  have hmem : ∀ v, v ∈ c.tail.support ↔ v ∈ c.support := by
    intro v
    constructor
    · intro hv
      rw [htail_support] at hv
      exact List.mem_of_mem_tail hv
    · intro hv
      rw [htail_support]
      obtain hvx | hv := List.mem_cons.mp (c.cons_tail_support ▸ hv)
      · subst v
        have hend : x ∈ c.tail.support := c.tail.end_mem_support
        rwa [htail_support] at hend
      · exact hv
  have hfinset : {v | v ∈ c.support}.toFinset = c.tail.support.toFinset := by
    ext v
    rw [Set.mem_toFinset, List.mem_toFinset]
    exact (hmem v).symm
  calc
    {v | v ∈ c.support}.ncard = c.tail.support.toFinset.card := by
      rw [Set.ncard_eq_toFinset_card']
      exact congrArg Finset.card hfinset
    _ = c.tail.support.length := List.toFinset_card_of_nodup hc.isPath_tail.support_nodup
    _ = c.length := by
      rw [c.tail.length_support, Walk.length_tail]
      have hpos := Walk.not_nil_iff_lt_length.mp hnil
      omega

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[mem_dropLast_support_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma IsCycle.mem_dropLast_support_iff {c : G.Walk x x}
  (hc : c.IsCycle) (v : V) :
  v ∈ c.support.dropLast ↔ v ∈ c.support := by
  constructor
  · exact List.mem_of_mem_dropLast
  · intro hv
    have hvTail : v ∈ c.support.tail := by
      obtain rfl | hv := List.mem_cons.mp (c.cons_tail_support ▸ hv)
      · exact c.end_mem_tail_support hc.not_nil
      · exact hv
    exact c.tail_support_perm_dropLast_support.mem_iff.mp hvTail

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[finLengthEquivSupport_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma IsCycle.finLengthEquivSupport_apply {c : G.Walk x x}
  (hc : c.IsCycle) (i : Fin c.length) :
  (hc.finLengthEquivSupport i).1 = c.getVert i := by
  classical
  simp [IsCycle.finLengthEquivSupport, c.getVert_eq_support_getElem i.isLt.le]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[mem_componentVertices_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma mem_componentVertices_iff (c : G.Walk x x)
  (D : c.outsideGraph.ConnectedComponent) (v : V) :
  v ∈ c.componentVertices D ↔
    ∃ hv : v ∉ c.support, (⟨v, hv⟩ : {w // w ∉ c.support}) ∈ D.supp := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hv, hD⟩
    exact ⟨⟨v, hv⟩, hD, rfl⟩

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[componentVertices_subset_compl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma componentVertices_subset_compl (c : G.Walk x x)
  (D : c.outsideGraph.ConnectedComponent) :
  c.componentVertices D ⊆ {v | v ∉ c.support} := by
  rintro v ⟨w, _, rfl⟩
  exact w.property

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[componentVertices_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma componentVertices_nonempty (c : G.Walk x x)
  (D : c.outsideGraph.ConnectedComponent) :
  (c.componentVertices D).Nonempty := by
  obtain ⟨w, hw⟩ := D.nonempty_supp
  exact ⟨w, w, hw, rfl⟩

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[support_subset_componentVertices_compl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma support_subset_componentVertices_compl (c : G.Walk x x)
  (D : c.outsideGraph.ConnectedComponent) :
  {v | v ∈ c.support} ⊆ (c.componentVertices D)ᶜ := by
  intro v hvc hvD
  exact (c.componentVertices_subset_compl D hvD) hvc

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[three_le_ncard_componentVertices_compl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma IsCycle.three_le_ncard_componentVertices_compl [Finite V]
  {c : G.Walk x x} (hc : c.IsCycle) (D : c.outsideGraph.ConnectedComponent) :
  3 ≤ (c.componentVertices D)ᶜ.ncard := by
  calc
    3 ≤ c.length := hc.three_le_length
    _ = {v | v ∈ c.support}.ncard := hc.ncard_support_eq_length.symm
    _ ≤ (c.componentVertices D)ᶜ.ncard :=
      Set.ncard_le_ncard (c.support_subset_componentVertices_compl D)

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[componentVertices_connected](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma componentVertices_connected (c : G.Walk x x)
  (D : c.outsideGraph.ConnectedComponent) :
  (G.induce (c.componentVertices D)).Connected := by
  apply D.connected_toSimpleGraph.map (componentGraphHom c D)
  rintro ⟨v, w, hw, hv⟩
  subst v
  exact ⟨⟨w, hw⟩, rfl⟩

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[mem_componentVertices_of_adj_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
component. -/
private lemma mem_componentVertices_of_adj_of_not_mem (c : G.Walk x x)
  (D : c.outsideGraph.ConnectedComponent) {u v : V}
  (hu : u ∈ c.componentVertices D) (huv : G.Adj u v) (hv : v ∉ c.support) :
  v ∈ c.componentVertices D := by
  obtain ⟨hu_out, huD⟩ := (c.mem_componentVertices_iff D u).mp hu
  apply (c.mem_componentVertices_iff D v).mpr
  refine ⟨hv, ?_⟩
  have hadj : c.outsideGraph.Adj ⟨u, hu_out⟩ ⟨v, hv⟩ := huv
  exact D.mem_supp_of_adj_mem_supp huD hadj

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[mem_support_of_adj_of_not_mem_componentVertices](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma mem_support_of_adj_of_not_mem_componentVertices (c : G.Walk x x)
  (D : c.outsideGraph.ConnectedComponent) {u v : V}
  (hu : u ∈ c.componentVertices D) (huv : G.Adj u v)
  (hv : v ∉ c.componentVertices D) :
  v ∈ c.support := by
  by_contra hvc
  exact hv (c.mem_componentVertices_of_adj_of_not_mem D hu huv hvc)

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[exists_two_attachments_of_component_ncard_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma IsVertexConnected.exists_two_attachments_of_component_ncard_eq_one
  [Fintype V] (hG : G.IsVertexConnected 2) (c : G.Walk x x)
  (D : c.outsideGraph.ConnectedComponent)
  (hcard : (c.componentVertices D).ncard = 1) :
  ∃ u ∈ c.componentVertices D, ∃ a ∈ c.support, ∃ b ∈ c.support,
    a ≠ b ∧ G.Adj u a ∧ G.Adj u b := by
  classical
  obtain ⟨u, hu⟩ := c.componentVertices_nonempty D
  obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp hcard
  have hwu : w = u := by
    rw [hw] at hu
    simpa using hu.symm
  subst w
  have hdeg : 1 < (G.neighborSet u).ncard := by
    rw [G.ncard_neighborSet]
    have := hG.two_le_degree u
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Set.one_lt_ncard_iff_nontrivial.mp hdeg
  have hua : G.Adj u a := (mem_neighborSet G u a).mp ha
  have hub : G.Adj u b := (mem_neighborSet G u b).mp hb
  have haC : a ∈ c.support := by
    by_contra haC
    have haD := c.mem_componentVertices_of_adj_of_not_mem D hu hua haC
    have hau : a = u := by simpa [hw] using haD
    exact (G.ne_of_adj hua) hau.symm
  have hbC : b ∈ c.support := by
    by_contra hbC
    have hbD := c.mem_componentVertices_of_adj_of_not_mem D hu hub hbC
    have hbu : b = u := by simpa [hw] using hbD
    exact (G.ne_of_adj hub) hbu.symm
  exact ⟨u, hu, a, haC, b, hbC, hab, hua, hub⟩
/-! ## ComponentContraction -/
namespace SimpleGraph
namespace Walk

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[contractOutside_component_adj_none](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
the cycle. -/
@[simp]
private lemma contractOutside_component_adj_none {c : G.Walk x x}
  (D : c.outsideGraph.ConnectedComponent) (u : c.componentVertices D) :
  (G.contractOutside (c.componentVertices D)).Adj (some u) none ↔
    ∃ v ∈ c.support, G.Adj u v := by
  rw [contractOutside_adj_none]
  constructor
  · rintro ⟨v, hvD, huv⟩
    exact ⟨v, c.mem_support_of_adj_of_not_mem_componentVertices D u.property huv hvD, huv⟩
  · rintro ⟨v, hvc, huv⟩
    exact ⟨v, c.support_subset_componentVertices_compl D hvc, huv⟩

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[contractOutside_square_adj_some_not_square](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
square uses the contraction vertex as its common neighbor. -/
private lemma contractOutside_square_adj_some_not_square {S : Set V} (a b : S)
  (hab : (G.contractOutside S).square.Adj (some a) (some b))
  (hnot : ¬G.square.Adj a b) :
  (G.contractOutside S).Adj (some a) none ∧
    (G.contractOutside S).Adj (some b) none := by
  have hne : (a : V) ≠ b := fun h ↦ hab.1 (congrArg some (Subtype.ext h))
  obtain hdirect | ⟨w, haw, hwb⟩ := hab.2
  · exact False.elim (hnot ⟨hne,
    Or.inl ((contractOutside_adj_some G S a b).mp hdirect)⟩)
  · cases w with
    | none => exact ⟨haw, hwb.symm⟩
    | some d =>
      have had : G.Adj a d := (contractOutside_adj_some G S a d).mp haw
      have hdb : G.Adj d b := (contractOutside_adj_some G S d b).mp hwb
      exact False.elim (hnot ⟨hne, Or.inr ⟨d, had, hdb⟩⟩)

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[component_contractOutside_isVertexConnected](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma IsCycle.component_contractOutside_isVertexConnected
  [Fintype V] {c : G.Walk x x} (_hc : c.IsCycle) (hG : G.IsVertexConnected 2)
  (D : c.outsideGraph.ConnectedComponent) [Fintype (c.componentVertices D)]
  (hD : 1 < (c.componentVertices D).ncard) :
  (G.contractOutside (c.componentVertices D)).IsVertexConnected 2 := by
  classical
  have hDcard : 1 < Fintype.card (c.componentVertices D) := by
    rwa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  apply hG.contractOutside hDcard (c.componentVertices_connected D)
  exact ⟨x, c.support_subset_componentVertices_compl D c.start_mem_support⟩

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[card_component_contractOutside_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma IsCycle.card_component_contractOutside_lt
  [Finite V] {c : G.Walk x x} (hc : c.IsCycle)
  (D : c.outsideGraph.ConnectedComponent) :
  Nat.card (Option (c.componentVertices D)) < Nat.card V := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite (c.componentVertices D)
  have hlt := card_contractOutside_lt (c.componentVertices D) (by
    have hthree := hc.three_le_ncard_componentVertices_compl D
    have hncard : (c.componentVertices D)ᶜ.ncard =
      Fintype.card ↥((c.componentVertices D)ᶜ) := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
    rw [hncard] at hthree
    omega)
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
/-! ## HamiltonianCycle helpers -/
namespace SimpleGraph

end SimpleGraph.Walk

namespace SimpleGraph

/--
[property_of_mem_edges_at_start](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
every cycle edge incident with the start. -/
private lemma Walk.IsCycle.property_of_mem_edges_at_start {V : Type*} {G : SimpleGraph V}
  {x v : V} {p : G.Walk x x} (hp : p.IsCycle) (P : V → Prop)
  (hfirst : P p.snd) (hlast : P p.penultimate)
  (he : s(x, v) ∈ p.edges) : P v := by
  have hadj : p.toSubgraph.Adj x v := Walk.adj_toSubgraph_iff_mem_edges.mpr he
  have hv : v ∈ p.toSubgraph.neighborSet x := hadj
  rw [hp.neighborSet_toSubgraph_endpoint] at hv
  obtain rfl | rfl := hv
  · exact hfirst
  · exact hlast
end SimpleGraph
/-! ## StrongSquareCycle listing -/
namespace SimpleGraph

end SimpleGraph

namespace SimpleGraph

/--
[toHasStrongSquareCycle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma StrongSquareCycleListing.toHasStrongSquareCycle
  {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x : V}
  (L : G.StrongSquareCycleListing x) : G.HasStrongSquareCycle x := by
  let l := L.vertices
  have hl_four : 4 ≤ l.length := L.four_le_length
  have hne : l ≠ [] := by simp [l, L.front_shape]
  have hhead : l.head hne = x := by
    simp [l, L.front_shape]
  have hgetLast : l.getLast hne = x := by
    simp [l, L.back_shape]
  let q := Walk.ofSupport l hne L.square_chain
  let p : G.square.Walk x x := q.copy hhead hgetLast
  have hp_length : p.length = l.length - 1 := by
    simp only [p, q, Walk.length_copy, Walk.length_ofSupport]
  have hp_not_nil : ¬p.Nil := by
    rw [Walk.not_nil_iff_lt_length, hp_length]
    omega
  have hp_support : p.support = l := by
    simp only [p, q, Walk.support_copy, Walk.support_ofSupport]
  have hp_cycle : p.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · rw [Walk.isPath_def, p.support_tail_of_not_nil hp_not_nil, hp_support]
      exact L.tail_nodup
    · omega
  have hp_hamiltonian : p.tail.IsHamiltonian := by
    apply hp_cycle.isPath_tail.isHamiltonian_of_mem
    intro v
    rw [p.support_tail_of_not_nil hp_not_nil, hp_support]
    exact L.mem_tail v
  have hsnd : p.snd = L.first := by
    calc
      p.snd = p.support[1]'(by simpa [Walk.not_nil_iff_lt_length] using hp_not_nil) :=
        p.snd_eq_support_getElem_one hp_not_nil
      _ = l[1]'(by omega) := by simp only [hp_support]
      _ = L.first := by simp [l, L.front_shape]
  have hpenultimate : p.penultimate = L.last := by
    calc
      p.penultimate = p.support[p.length - 1] :=
        p.support_getElem_length_sub_one_eq_penultimate.symm
      _ = l[p.length - 1]'(by rw [← hp_support]; get_elem_tactic) := by
        simp only [hp_support]
      _ = l[l.length - 2]'(by omega) := by
        congr 1
        omega
      _ = L.last := by simp [l, L.back_shape]
  refine ⟨p, ⟨hp_cycle, hp_hamiltonian⟩, ?_, ?_⟩
  · rw [hsnd]
    exact L.first_adj
  · rw [hpenultimate]
    exact L.last_adj
end SimpleGraph
/-! ## ComponentTrailCover -/
namespace SimpleGraph
namespace Walk
universe u

end SimpleGraph

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[singletonCoverEnds_mem_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma singletonCoverEnds_mem_left (u a b : V) (i : Fin 2) :
  u ∈ singletonCoverEnds u a b i := by
  by_cases hi : i = 0
  · simp [singletonCoverEnds, hi]
  · simp [singletonCoverEnds, hi]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[singletonComponentTrailCover](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma IsVertexConnected.singletonComponentTrailCover [Fintype V]
  (hG : G.IsVertexConnected 2) (c : G.Walk x x)
  (D : c.outsideGraph.ConnectedComponent)
  (hcard : (c.componentVertices D).ncard = 1) :
  Nonempty (c.ComponentTrailCover D) := by
  classical
  obtain ⟨u, hu, a, ha, b, hb, hab, hua, hub⟩ :=
    SimpleGraph.Walk.IsVertexConnected.exists_two_attachments_of_component_ncard_eq_one
      hG c D hcard
  obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp hcard
  have hwu : w = u := by
    rw [hw] at hu
    simpa using hu.symm
  subst w
  let M : EdgeIndexedMultigraph V (ULift.{u} (Fin 2)) := {
    ends := fun i ↦ singletonCoverEnds u a b i.down
    loopless := by
      intro i v hiv
      have hedge : singletonCoverEnds u a b i.down ∈ G.edgeSet := by
        by_cases hi : i.down = 0
        · simp [singletonCoverEnds, hi, G.mem_edgeSet, hua]
        · simp [singletonCoverEnds, hi, G.mem_edgeSet, hub]
      rw [hiv] at hedge
      exact G.loopless.irrefl v (G.mem_edgeSet.mp hedge) }
  refine ⟨{
    Edge := ULift.{u} (Fin 2)
    edge_finite := inferInstance
    multigraph := M
    square_adj := ?_
    meets_component := ?_
    endpoints_mem := ?_
    cycle_edge := ?_
    degree_eq_two := ?_
    reachable_cycle := ?_ }⟩
  · intro i
    obtain ⟨i⟩ := i
    by_cases hi : i = 0
    · subst i
      exact G.square.mem_edgeSet.mpr ⟨G.ne_of_adj hua, Or.inl hua⟩
    · have hi1 := Fin.eq_one_of_ne_zero i hi
      subst i
      exact G.square.mem_edgeSet.mpr ⟨G.ne_of_adj hub, Or.inl hub⟩
  · intro i
    exact ⟨u, hu, singletonCoverEnds_mem_left u a b i.down⟩
  · intro i v hv
    obtain ⟨i⟩ := i
    by_cases hi : i = 0
    · subst i
      change v ∈ s(u, a) at hv
      obtain rfl | rfl := Sym2.mem_iff.mp hv
      · exact Or.inl hu
      · exact Or.inr ha
    · have hi1 := Fin.eq_one_of_ne_zero i hi
      subst i
      change v ∈ s(u, b) at hv
      obtain rfl | rfl := Sym2.mem_iff.mp hv
      · exact Or.inl hu
      · exact Or.inr hb
  · intro i v z hiz _
    obtain ⟨i⟩ := i
    have hedge : s(v, z) ∈ G.edgeSet := by
      rw [← hiz]
      by_cases hi : i = 0
      · simpa [M, singletonCoverEnds, hi] using G.mem_edgeSet.mpr hua
      · simpa [M, singletonCoverEnds, hi] using G.mem_edgeSet.mpr hub
    exact G.mem_edgeSet.mp hedge
  · intro v hv
    have hvu : v = u := by
      simpa [hw] using hv
    subst v
    have hset : {i : ULift.{u} (Fin 2) | M.Inc u i} = Set.univ := by
      ext i
      constructor
      · intro
        trivial
      · intro
        exact singletonCoverEnds_mem_left u a b i.down
    rw [EdgeIndexedMultigraph.degree, hset, Set.ncard_univ, Nat.card_ulift,
      Nat.card_fin]
  · intro v hv
    have hvu : v = u := by
      simpa [hw] using hv
    subst v
    refine ⟨a, ha, ?_⟩
    apply Adj.reachable
    apply M.underlying_adj.mpr
    exact ⟨ULift.up 0, by simp [M, singletonCoverEnds]⟩

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[nontrivialCoverEdgeFinite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma nontrivialCoverEdgeFinite {S : Set V} [Finite S]
  {p : (G.contractOutside S).square.Walk none none} :
  Finite (NontrivialCoverEdge p) := by
  classical
  let _ := Fintype.ofFinite S
  let f : NontrivialCoverEdge p →
    Sym2 (Option S) ⊕ (Sym2 (Option S) × S)
    | Sum.inl e => Sum.inl e.1.1
    | Sum.inr i => Sum.inr (i.edge.1, i.vertex)
  apply Finite.of_injective f
  intro e e' he
  cases e with
  | inl e =>
    cases e' with
    | inl e' =>
      apply congrArg Sum.inl
      apply Subtype.ext
      apply Subtype.ext
      exact Sum.inl.inj he
    | inr i => contradiction
  | inr i =>
    cases e' with
    | inl e' => contradiction
    | inr i' =>
      cases i with
      | mk ie iv im ib =>
        cases i' with
        | mk je jv jm jb =>
          have hi : (ie.1, iv) = (je.1, jv) := Sum.inr.inj he
          have hie : ie = je := Subtype.ext (congrArg Prod.fst hi)
          subst je
          have hiv : iv = jv := congrArg Prod.snd hi
          subst jv
          rfl

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[contractOutside_adj_none_of_strong_cycle_edge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma contractOutside_adj_none_of_strong_cycle_edge {S : Set V}
  [DecidableEq (Option S)]
  {p : (G.contractOutside S).square.Walk none none}
  (hp : p.IsHamiltonianCycle)
  (hfirst : (G.contractOutside S).Adj none p.snd)
  (hlast : (G.contractOutside S).Adj p.penultimate none)
  (d : S) (w : Option S) (he : s(some d, w) ∈ p.edges)
  (hbad : ∀ e, w = some e → ¬G.square.Adj d e) :
  (G.contractOutside S).Adj (some d) none := by
  cases w with
  | none =>
    have he' : s(none, some d) ∈ p.edges := by
      rwa [Sym2.eq_swap]
    exact (hp.1.property_of_mem_edges_at_start
      ((G.contractOutside S).Adj none ·) hfirst hlast.symm he').symm
  | some e =>
    have hadj : (G.contractOutside S).square.Adj (some d) (some e) :=
      (G.contractOutside S).square.mem_edgeSet.mp (p.edges_subset_edgeSet he)
    exact (Walk.contractOutside_square_adj_some_not_square d e hadj
      (hbad e rfl)).1

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cycleCoverEdge_mem_edges](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cycleCoverEdge_mem_edges {S : Set V}
  {p : (G.contractOutside S).square.Walk none none} (e : CycleCoverEdge p) :
  (e : Sym2 (Option S)) ∈ p.edges := by
  have he := e.property
  change (e : Sym2 (Option S)) ∈ p.toSubgraph.spanningCoe.edgeSet at he
  rw [Subgraph.edgeSet_spanningCoe] at he
  exact p.mem_edges_toSubgraph.mp he

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[exists_attachment](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma BadCycleIncidence.exists_attachment [DecidableEq V]
  {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
  {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
  (hp : p.IsHamiltonianCycle)
  (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
  (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
  (i : BadCycleIncidence p) :
  ∃ v ∈ c.support, G.Adj i.vertex v := by
  obtain ⟨w, heq⟩ := Sym2.mem_iff_exists.mp i.mem_edge
  have he : s(some i.vertex, w) ∈ p.edges := by
    rw [← heq]
    exact cycleCoverEdge_mem_edges i.edge
  have hbad : ∀ e, w = some e → ¬G.square.Adj i.vertex e := by
    intro e hwe hadj
    apply i.not_good
    exact ⟨i.vertex, e, heq.trans (congrArg (s(some i.vertex, ·)) hwe), hadj⟩
  have hnone := contractOutside_adj_none_of_strong_cycle_edge hp hfirst hlast
    i.vertex w he hbad
  exact (contractOutside_component_adj_none D i.vertex).mp hnone

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[attachment_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma BadCycleIncidence.attachment_mem [DecidableEq V]
  {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
  {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
  (hp : p.IsHamiltonianCycle)
  (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
  (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
  (i : BadCycleIncidence p) : i.attachment D hp hfirst hlast ∈ c.support :=
  (i.exists_attachment D hp hfirst hlast).choose_spec.1

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[adj_attachment](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma BadCycleIncidence.adj_attachment [DecidableEq V]
  {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
  {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
  (hp : p.IsHamiltonianCycle)
  (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
  (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
  (i : BadCycleIncidence p) : G.Adj i.vertex (i.attachment D hp hfirst hlast) :=
  (i.exists_attachment D hp hfirst hlast).choose_spec.2

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[nontrivialCoverEnds_meets_component](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma nontrivialCoverEnds_meets_component [DecidableEq V]
  {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
  {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
  (hp : p.IsHamiltonianCycle)
  (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
  (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
  (e : NontrivialCoverEdge p) :
  ∃ v ∈ c.componentVertices D,
    v ∈ nontrivialCoverEnds D hp hfirst hlast e := by
  cases e with
  | inl e =>
    exact ⟨goodCycleCoverLeft e, (goodCycleCoverLeft e).property,
      Sym2.mem_iff.mpr (Or.inl rfl)⟩
  | inr i =>
    exact ⟨i.vertex, i.vertex.property, Sym2.mem_iff.mpr (Or.inl rfl)⟩

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[nontrivialCoverEnds_endpoints_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma nontrivialCoverEnds_endpoints_mem [DecidableEq V]
  {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
  {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
  (hp : p.IsHamiltonianCycle)
  (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
  (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
  (e : NontrivialCoverEdge p) (v : V)
  (hv : v ∈ nontrivialCoverEnds D hp hfirst hlast e) :
  v ∈ c.componentVertices D ∨ v ∈ c.support := by
  cases e with
  | inl e =>
    obtain hv | hv := Sym2.mem_iff.mp hv
    · exact Or.inl (hv.symm ▸ (goodCycleCoverLeft e).property)
    · exact Or.inl (hv.symm ▸ (goodCycleCoverRight e).property)
  | inr i =>
    obtain hv | hv := Sym2.mem_iff.mp hv
    · exact Or.inl (hv.symm ▸ i.vertex.property)
    · exact Or.inr (hv.symm ▸ i.attachment_mem D hp hfirst hlast)

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[nontrivialCoverEnds_cycle_edge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma nontrivialCoverEnds_cycle_edge [DecidableEq V]
  {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
  {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
  (hp : p.IsHamiltonianCycle)
  (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
  (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
  (e : NontrivialCoverEdge p) (u v : V)
  (he : nontrivialCoverEnds D hp hfirst hlast e = s(u, v))
  (hcycle : u ∈ c.support ∨ v ∈ c.support) : G.Adj u v := by
  cases e with
  | inl e =>
    exfalso
    obtain hu | hv := hcycle
    · have huEnds : u ∈ nontrivialCoverEnds D hp hfirst hlast (Sum.inl e) :=
      he.symm ▸ Sym2.mem_iff.mpr (Or.inl rfl)
      change u ∈ s((goodCycleCoverLeft e : V), (goodCycleCoverRight e : V)) at huEnds
      obtain hlu | hru := Sym2.mem_iff.mp huEnds
      · exact (c.componentVertices_subset_compl D (goodCycleCoverLeft e).property)
        (hlu ▸ hu)
      · exact (c.componentVertices_subset_compl D (goodCycleCoverRight e).property)
        (hru ▸ hu)
    · have hvEnds : v ∈ nontrivialCoverEnds D hp hfirst hlast (Sum.inl e) :=
      he.symm ▸ Sym2.mem_iff.mpr (Or.inr rfl)
      change v ∈ s((goodCycleCoverLeft e : V), (goodCycleCoverRight e : V)) at hvEnds
      obtain hlv | hrv := Sym2.mem_iff.mp hvEnds
      · exact (c.componentVertices_subset_compl D (goodCycleCoverLeft e).property)
        (hlv ▸ hv)
      · exact (c.componentVertices_subset_compl D (goodCycleCoverRight e).property)
        (hrv ▸ hv)
  | inr i =>
    have hi := i.adj_attachment D hp hfirst hlast
    apply G.mem_edgeSet.mp
    rw [← he]
    exact G.mem_edgeSet.mpr hi

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[nontrivialCoverMultigraph_degree_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma nontrivialCoverMultigraph_degree_eq_two [Finite V]
  [DecidableEq V] {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
  {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
  (hp : p.IsHamiltonianCycle)
  (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
  (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
  (d : c.componentVertices D) :
  (nontrivialCoverMultigraph D hp hfirst hlast).degree d = 2 := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite (Option (c.componentVertices D))
  let H := p.toSubgraph.spanningCoe
  have hsubdegree : p.toSubgraph.degree (some d) = 2 := by
    rw [Subgraph.degree, Set.fintypeCard_eq_ncard]
    exact hp.1.ncard_neighborSet_toSubgraph_eq_two (hp.mem_support (some d))
  have hincidence : Nat.card (H.incidenceSet (some d)) = 2 := by
    rw [Nat.card_eq_fintype_card, H.card_incidenceSet_eq_degree]
    change p.toSubgraph.spanningCoe.degree (some d) = 2
    rwa [Subgraph.degree_spanningCoe]
  rw [EdgeIndexedMultigraph.degree, ← Nat.card_coe_set_eq]
  calc
    Nat.card {e : NontrivialCoverEdge p |
      (d : V) ∈ nontrivialCoverEnds D hp hfirst hlast e} =
      Nat.card (H.incidenceSet (some d)) :=
      Nat.card_congr (cycleCoverIncidenceEquiv D hp hfirst hlast d).symm
    _ = 2 := hincidence

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[not_of_none_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma IsGoodCycleCoverEdge.not_of_none_mem {S : Set V}
  {p : (G.contractOutside S).square.Walk none none} (e : CycleCoverEdge p)
  (hnone : none ∈ (e : Sym2 (Option S))) : ¬IsGoodCycleCoverEdge e := by
  rintro ⟨a, b, he, _⟩
  rw [he] at hnone
  simp at hnone

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[trailSystemMultigraph_square_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma trailSystemMultigraph_square_adj
  (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  (e : c.TrailSystemEdge cover) :
  (c.trailSystemMultigraph cover).ends e ∈ G.square.edgeSet := by
  cases e with
  | inl i =>
    have h := c.adj_getVert_succ i.down.isLt
    exact G.square.mem_edgeSet.mpr ⟨G.ne_of_adj h, Or.inl h⟩
  | inr e => exact (cover e.1).square_adj e.2

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[trailSystemMultigraph_cycle_edge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma trailSystemMultigraph_cycle_edge
  (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  (e : c.TrailSystemEdge cover) (u v : V)
  (he : (c.trailSystemMultigraph cover).ends e = s(u, v))
  (hcycle : u ∈ c.support ∨ v ∈ c.support) : G.Adj u v := by
  cases e with
  | inl i =>
    apply G.mem_edgeSet.mp
    rw [← he]
    exact G.mem_edgeSet.mpr (c.adj_getVert_succ i.down.isLt)
  | inr e => exact (cover e.1).cycle_edge e.2 u v he hcycle

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[connected_of_cycle_reachable_and_component_covers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
cover maps into it. -/
private lemma connected_of_cycle_reachable_and_component_covers
  (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  (H : SimpleGraph V)
  (hcycle : ∀ v, v ∈ c.support → H.Reachable v x)
  (hcover : ∀ D, (cover D).multigraph.underlying →g H)
  (hcover_id : ∀ D v, hcover D v = v) : H.Connected := by
  refine { preconnected := ?_, nonempty := ⟨x⟩ }
  intro u v
  suffices ∀ w, H.Reachable w x by
    exact (this u).trans (this v).symm
  intro w
  by_cases hw : w ∈ c.support
  · exact hcycle w hw
  · let w' : {z : V // z ∉ c.support} := ⟨w, hw⟩
    let D := c.outsideGraph.connectedComponentMk w'
    have hwD : w ∈ c.componentVertices D := by
      apply (c.mem_componentVertices_iff D w).mpr
      exact ⟨hw, ConnectedComponent.connectedComponentMk_mem⟩
    obtain ⟨z, hzc, hwz⟩ := (cover D).reachable_cycle w hwD
    have hwz' : H.Reachable w z := by
      simpa only [hcover_id] using hwz.map (hcover D)
    exact hwz'.trans (hcycle z hzc)

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[mem_componentVertices_outsideComponent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma mem_componentVertices_outsideComponent (c : G.Walk x x)
  {v : V} (hv : v ∉ c.support) :
  v ∈ c.componentVertices (outsideComponent c hv) := by
  apply (c.mem_componentVertices_iff (outsideComponent c hv) v).mpr
  exact ⟨hv, ConnectedComponent.connectedComponentMk_mem⟩

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[trailSystemMultigraph_degree_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma trailSystemMultigraph_degree_eq_two [Finite V] (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  {v : V} (hv : v ∉ c.support) :
  (c.trailSystemMultigraph cover).degree v = 2 := by
  let D := outsideComponent c hv
  calc
    (c.trailSystemMultigraph cover).degree v =
      Nat.card {e : c.TrailSystemEdge cover |
        (c.trailSystemMultigraph cover).Inc v e} := by
      rw [EdgeIndexedMultigraph.degree, Nat.card_coe_set_eq]
    _ = Nat.card {e : (cover D).Edge | (cover D).multigraph.Inc v e} :=
      Nat.card_congr (trailSystemIncidenceEquiv c cover hv).symm
    _ = (cover D).multigraph.degree v := by
      rw [EdgeIndexedMultigraph.degree, Nat.card_coe_set_eq]
    _ = 2 := (cover D).degree_eq_two v (mem_componentVertices_outsideComponent c hv)

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[trailSystemMultigraph_cycle_degree_sum_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma trailSystemMultigraph_cycle_degree_sum_even [Finite V]
  (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D) :
  Even (∑ i : Fin c.length,
    (c.trailSystemMultigraph cover).degree (c.getVert i)) := by
  classical
  let _ := Fintype.ofFinite V
  let M := c.trailSystemMultigraph cover
  have htotal : Even (∑ v : V, M.degree v) := M.even_sum_degree
  let cycleVertices : Finset V := Finset.univ.filter fun v ↦ v ∈ c.support
  let outsideVertices : Finset V := Finset.univ.filter fun v ↦ v ∉ c.support
  have hsplit : (∑ v ∈ cycleVertices, M.degree v) +
    (∑ v ∈ outsideVertices, M.degree v) = ∑ v : V, M.degree v := by
    simpa [cycleVertices, outsideVertices] using
      Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun v : V ↦ v ∈ c.support) (fun v ↦ M.degree v)
  rw [← hsplit] at htotal
  have hout : Even (∑ v ∈ outsideVertices, M.degree v) := by
    have heq : (∑ v ∈ outsideVertices, M.degree v) =
      ∑ _v ∈ outsideVertices, 2 := by
      apply Finset.sum_congr rfl
      intro v hv
      apply c.trailSystemMultigraph_degree_eq_two cover
      simpa [outsideVertices] using hv
    rw [heq]
    exact ⟨outsideVertices.card, by simp; omega⟩
  have hsupport : Even (∑ v ∈ cycleVertices, M.degree v) :=
    (Nat.even_add.mp htotal).mpr hout
  have hsum : (∑ i : Fin c.length, M.degree (c.getVert i)) =
    ∑ v ∈ cycleVertices, M.degree v := by
    refine Finset.sum_bij (s := (Finset.univ : Finset (Fin c.length)))
      (t := cycleVertices) (fun i _ ↦ c.getVert i) ?_ ?_ ?_ ?_
    · intro i _
      simp [cycleVertices]
    · intro i _ j _ hij
      apply hc.finLengthEquivSupport.injective
      apply Subtype.ext
      simpa using hij
    · intro v hv
      have hvc : v ∈ c.support := by simpa [cycleVertices] using hv
      let v' : {z : V // z ∈ c.support} := ⟨v, hvc⟩
      let i := hc.finLengthEquivSupport.symm v'
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply (hc.finLengthEquivSupport_apply i).symm.trans
      simpa only [i, v'] using
        congrArg Subtype.val (hc.finLengthEquivSupport.apply_symm_apply v')
    · intro i _
      rfl
  rwa [hsum]
/-! ## CycleParity -/
open scoped BigOperators

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[getVert_injective_fin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma IsCycle.getVert_injective_fin {c : G.Walk x x} (hc : c.IsCycle) :
  Function.Injective (fun i : Fin c.length ↦ c.getVert i) := by
  intro i j hij
  apply hc.finLengthEquivSupport.injective
  apply Subtype.ext
  simpa using hij

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[getVert_succ_eq_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma IsCycle.getVert_succ_eq_add_one {c : G.Walk x x} (hc : c.IsCycle)
  [NeZero c.length] (i : Fin c.length) :
  c.getVert (i.val + 1) = c.getVert (i + 1 : Fin c.length) := by
  have hlength : 1 < c.length := lt_of_lt_of_le (by omega) hc.three_le_length
  have hone : (1 : Fin c.length).val = 1 := Nat.mod_eq_of_lt hlength
  by_cases hlt : i.val + 1 < c.length
  · have hval : (i + 1 : Fin c.length).val = i.val + 1 := by
    have haddlt : i.val + (1 : Fin c.length).val < c.length := by
      rwa [hone]
    rw [Fin.val_add_eq_of_add_lt haddlt, hone]
    rw [hval]
  · have heq : i.val + 1 = c.length := by omega
    have hzero : (i + 1 : Fin c.length) = 0 := by
      apply Fin.ext
      simp [Fin.val_add, heq]
    rw [heq, c.getVert_length, hzero]
    change x = c.getVert 0
    exact c.getVert_zero.symm

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[sub_one_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma IsCycle.sub_one_ne {c : G.Walk x x} (hc : c.IsCycle)
  [NeZero c.length] (i : Fin c.length) : i - 1 ≠ i := by
  intro hi
  have hadd := congrArg (fun z : Fin c.length ↦ z + 1) hi
  rw [sub_add_cancel] at hadd
  have hzero : (0 : Fin c.length) = 1 := by
    apply add_left_cancel (a := i)
    simpa using hadd
  have hlength : 1 < c.length := lt_of_lt_of_le (by omega) hc.three_le_length
  have hval := congrArg (fun z : Fin c.length ↦ z.val) hzero
  simp at hval
  omega

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[trailSystemMultigraph_degree_eq_two_of_isBoundVertex](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
system. -/
private lemma trailSystemMultigraph_degree_eq_two_of_isBoundVertex [Finite V]
  (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length]
  (i : Fin c.length) (hbound : c.IsBoundVertex (c.getVert i)) :
  (c.trailSystemMultigraph cover).degree (c.getVert i) = 2 := by
  calc
    (c.trailSystemMultigraph cover).degree (c.getVert i) =
      Nat.card {e : c.TrailSystemEdge cover //
        (c.trailSystemMultigraph cover).Inc (c.getVert i) e} := by
      exact (Nat.card_coe_set_eq
        {e : c.TrailSystemEdge cover |
          (c.trailSystemMultigraph cover).Inc (c.getVert i) e}).symm
    _ = Nat.card (Fin 2) := Nat.card_congr (boundIncidenceEquiv c hc cover i hbound)
    _ = 2 := Nat.card_fin 2

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[cycleCopyMultigraph_degree_getVert](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
edges. -/
private lemma cycleCopyMultigraph_degree_getVert {c : G.Walk x x}
  (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
  (q : CyclicParityCompletion d) (i : Fin c.length) :
  (c.cycleCopyMultigraph q).degree (c.getVert i) =
    q.copies (i - 1) + q.copies i := by
  calc
    (c.cycleCopyMultigraph q).degree (c.getVert i) =
      Nat.card {e : c.CycleCopyEdge q //
        (c.cycleCopyMultigraph q).Inc (c.getVert i) e} := by
      rw [EdgeIndexedMultigraph.degree]
      exact (Nat.card_coe_set_eq
        {e : c.CycleCopyEdge q |
          (c.cycleCopyMultigraph q).Inc (c.getVert i) e}).symm
    _ = Nat.card (Fin (q.copies (i - 1)) ⊕ Fin (q.copies i)) :=
      Nat.card_congr (cycleCopyIncidenceEquiv hc q i)
    _ = Nat.card (Fin (q.copies (i - 1))) + Nat.card (Fin (q.copies i)) :=
      Nat.card_sum
    _ = q.copies (i - 1) + q.copies i := by
      rw [Nat.card_fin, Nat.card_fin]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[cycleCopyMultigraph_mem_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cycleCopyMultigraph_mem_edgeSet (c : G.Walk x x)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (e : c.CycleCopyEdge q) :
  (c.cycleCopyMultigraph q).ends e ∈ G.edgeSet :=
G.mem_edgeSet.mpr (c.adj_getVert_succ e.1.isLt)

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[cycleCopyMultigraph_degree_eq_zero_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cycleCopyMultigraph_degree_eq_zero_of_not_mem {c : G.Walk x x}
  (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
  (q : CyclicParityCompletion d) {v : V} (hv : v ∉ c.support) :
  (c.cycleCopyMultigraph q).degree v = 0 := by
  rw [EdgeIndexedMultigraph.degree, Set.ncard_eq_zero]
  ext e
  rw [Set.mem_empty_iff_false, iff_false]
  intro he
  obtain ⟨i, k⟩ := e
  change v ∈ s(c.getVert i, c.getVert (i.val + 1)) at he
  obtain rfl | rfl := Sym2.mem_iff.mp he
  · exact hv (c.getVert_mem_support i)
  · apply hv
    rw [hc.getVert_succ_eq_add_one]
    exact c.getVert_mem_support (i + 1 : Fin c.length)
/-! ## CycleEulerization -/
namespace SimpleGraph
namespace Walk

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {G : SimpleGraph V} {x : V}
/--
[cycleEulerization_even_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cycleEulerization_even_degree [Finite V]
  (c : G.Walk x x) (hc : c.IsCycle) [NeZero c.length]
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  (v : V) : Even (c.cycleEulerizationMultigraph hc cover |>.degree v) := by
  classical
  let q := c.cycleEulerizationCompletion hc cover
  rw [cycleEulerizationMultigraph, EdgeIndexedMultigraph.disjointSum_degree]
  by_cases hv : v ∈ c.support
  · let v' : {z : V // z ∈ c.support} := ⟨v, hv⟩
    let i := hc.finLengthEquivSupport.symm v'
    have hvi : c.getVert i = v := by
      apply (hc.finLengthEquivSupport_apply i).symm.trans
      simpa only [i, v'] using
        congrArg Subtype.val (hc.finLengthEquivSupport.apply_symm_apply v')
    rw [← hvi, c.cycleCopyMultigraph_degree_getVert hc]
    change Even ((c.trailSystemMultigraph cover).degree (c.getVert i) +
      (q.copies (i - 1) + q.copies i))
    simpa only [Nat.add_assoc] using q.even_at i
  · rw [c.trailSystemMultigraph_degree_eq_two cover hv,
    c.cycleCopyMultigraph_degree_eq_zero_of_not_mem hc _ hv]
    exact even_two
/-! ## TransitionCompression -/
namespace SimpleGraph
namespace EdgeIndexedMultigraph

end SimpleGraph.Walk

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[degree_eq_sum_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma degree_eq_sum_incidence [Fintype E] (v : V)
  [DecidablePred (M.Inc v)] :
  M.degree v = ∑ e : E, if M.Inc v e then 1 else 0 := by
  unfold degree
  have hset : {e : E | M.Inc v e} =
    (Finset.univ.filter (M.Inc v) : Finset E) := by
    ext e
    simp
  rw [hset, Set.ncard_coe_finset, Finset.sum_boole]
  congr 1

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[edgePartitionEquiv_symm_apply_inl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma edgePartitionEquiv_symm_apply_inl {T : Type*}
  (transition : T → M.EdgeTransition)
  (hinj : Function.Injective (M.transitionEdge transition))
  (e : M.UnpairedTransitionEdge transition) :
  (M.edgePartitionEquiv transition hinj).symm (Sum.inl e) = e.1 := by
  simp [edgePartitionEquiv]

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[edgePartitionEquiv_symm_apply_inr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma edgePartitionEquiv_symm_apply_inr {T : Type*}
  (transition : T → M.EdgeTransition)
  (hinj : Function.Injective (M.transitionEdge transition)) (p : T × Fin 2) :
  (M.edgePartitionEquiv transition hinj).symm (Sum.inr p) =
    M.transitionEdge transition p := by
  simp [edgePartitionEquiv]

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[edgePartitionEquiv_apply_unpaired](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma edgePartitionEquiv_apply_unpaired {T : Type*}
  (transition : T → M.EdgeTransition)
  (hinj : Function.Injective (M.transitionEdge transition))
  (e : M.UnpairedTransitionEdge transition) :
  M.edgePartitionEquiv transition hinj e.1 = Sum.inl e := by
  apply (M.edgePartitionEquiv transition hinj).symm.injective
  simp

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[edgePartitionEquiv_apply_transitionEdge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma edgePartitionEquiv_apply_transitionEdge {T : Type*}
  (transition : T → M.EdgeTransition)
  (hinj : Function.Injective (M.transitionEdge transition)) (p : T × Fin 2) :
  M.edgePartitionEquiv transition hinj (M.transitionEdge transition p) =
    Sum.inr p := by
  apply (M.edgePartitionEquiv transition hinj).symm.injective
  simp

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[degree_cast_eq_sum_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma degree_cast_eq_sum_incidence [Fintype E] (v : V) :
  (M.degree v : ZMod 2) = ∑ e : E, M.incidenceWeight v e := by
  classical
  rw [degree_eq_sum_incidence]
  simp [incidenceWeight]

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[transition_incidence_parity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma transition_incidence_parity {T : Type*}
  (transition : T → M.EdgeTransition) (t : T) (v : V) :
  M.incidenceWeight v (transition t).left +
    M.incidenceWeight v (transition t).right =
    (M.compressTransitions transition).incidenceWeight v (Sum.inr t) := by
  classical
  have hbefore : (transition t).before ≠ (transition t).center := by
    intro h
    apply M.loopless (transition t).left (transition t).before
    simpa [h] using (transition t).left_ends
  have hafter : (transition t).center ≠ (transition t).after := by
    intro h
    apply M.loopless (transition t).right (transition t).center
    simpa [h] using (transition t).right_ends
  by_cases hvbefore : v = (transition t).before
  · subst v
    simp only [incidenceWeight, Inc, (transition t).left_ends, Sym2.mem_iff,
      hbefore, or_false, ↓reduceIte, (transition t).right_ends,
      (transition t).before_ne_after, or_self, add_zero, compressTransitions]
  · by_cases hvcenter : v = (transition t).center
    · subst v
      simp only [incidenceWeight, Inc, (transition t).left_ends, Sym2.mem_iff,
        Ne.symm hbefore, or_true, ↓reduceIte, (transition t).right_ends, hafter,
        or_false, compressTransitions, or_self]
      change ((2 : ℕ) : ZMod 2) = 0
      exact ZMod.natCast_eq_zero_iff_even.mpr even_two
    · by_cases hvafter : v = (transition t).after
      · subst v
        simp only [incidenceWeight, Inc, (transition t).left_ends, Sym2.mem_iff,
          hvbefore, hvcenter, or_self, ↓reduceIte, (transition t).right_ends,
          or_true, zero_add, compressTransitions]
      · simp [incidenceWeight, Inc, compressTransitions, (transition t).left_ends,
        (transition t).right_ends, Sym2.mem_iff, hvbefore, hvcenter, hvafter]

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[compressTransitions_even_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma compressTransitions_even_degree {T : Type*} [Finite E] [Finite T]
  (transition : T → M.EdgeTransition)
  (hinj : Function.Injective (M.transitionEdge transition))
  (heven : ∀ v, Even (M.degree v)) (v : V) :
  Even ((M.compressTransitions transition).degree v) := by
  classical
  let _ := Fintype.ofFinite E
  let _ := Fintype.ofFinite T
  apply ZMod.natCast_eq_zero_iff_even.mp
  calc
    ((M.compressTransitions transition).degree v : ZMod 2) =
      ∑ e : M.CompressedTransitionEdge transition,
        (M.compressTransitions transition).incidenceWeight v e :=
      (M.compressTransitions transition).degree_cast_eq_sum_incidence v
    _ = (∑ e : M.UnpairedTransitionEdge transition, M.incidenceWeight v e.1) +
      ∑ t : T, (M.compressTransitions transition).incidenceWeight v (Sum.inr t) := by
      rw [Fintype.sum_sum_type]
      rfl
    _ = (∑ e : M.UnpairedTransitionEdge transition, M.incidenceWeight v e.1) +
      ∑ t : T, (M.incidenceWeight v (transition t).left +
        M.incidenceWeight v (transition t).right) := by
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      exact (M.transition_incidence_parity transition t v).symm
    _ = (∑ e : M.UnpairedTransitionEdge transition, M.incidenceWeight v e.1) +
      ∑ p : T × Fin 2, M.incidenceWeight v (M.transitionEdge transition p) := by
      rw [Fintype.sum_prod_type]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      rw [Fin.sum_univ_two]
      simp [transitionEdge]
    _ = ∑ e : E, M.incidenceWeight v e := by
      calc
        (∑ e : M.UnpairedTransitionEdge transition, M.incidenceWeight v e.1) +
          ∑ p : T × Fin 2, M.incidenceWeight v (M.transitionEdge transition p) =
          ∑ z : M.UnpairedTransitionEdge transition ⊕ (T × Fin 2),
            M.incidenceWeight v ((M.edgePartitionEquiv transition hinj).symm z) := by
          rw [Fintype.sum_sum_type]
          simp
        _ = ∑ e : E, M.incidenceWeight v e :=
          (M.edgePartitionEquiv transition hinj).symm.sum_comp
            (M.incidenceWeight v)
    _ = (M.degree v : ZMod 2) := (M.degree_cast_eq_sum_incidence v).symm
    _ = 0 := ZMod.natCast_eq_zero_iff_even.mpr (heven v)

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[expandTransitions_edges_perm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma expandTransitions_edges_perm [DecidableEq V] {T : Type*}
  (transition : T → M.EdgeTransition) {u v : V}
  (p : (M.compressTransitions transition).IndexedWalk u v) :
  (M.expandTransitions transition p).edges.Perm
    (p.edges.flatMap (M.transitionExpansionEdges transition)) :=
  (M.expandTransitionsWithEdges transition p).edges_perm

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[expandTransitions_edges_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma expandTransitions_edges_adjacent [DecidableEq V] {T : Type*}
  (transition : T → M.EdgeTransition) {u v : V}
  (p : (M.compressTransitions transition).IndexedWalk u v) (t : T)
  (ht : Sum.inr t ∈ p.edges) :
  EdgesAdjacent (transition t).left (transition t).right
    (M.expandTransitions transition p).edges :=
  (M.expandTransitionsWithEdges transition p).edges_adjacent t ht

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[transitionOwner_unpaired](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma transitionOwner_unpaired {T : Type*}
  (transition : T → M.EdgeTransition)
  (hinj : Function.Injective (M.transitionEdge transition))
  (e : M.UnpairedTransitionEdge transition) :
  M.transitionOwner transition hinj e.1 = Sum.inl e := by
  classical
  have hpart : M.edgePartitionEquiv transition hinj e.1 = Sum.inl e := by
    apply (M.edgePartitionEquiv transition hinj).symm.injective
    simp
  simp [transitionOwner, hpart]

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[transitionOwner_transitionEdge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma transitionOwner_transitionEdge {T : Type*}
  (transition : T → M.EdgeTransition)
  (hinj : Function.Injective (M.transitionEdge transition)) (p : T × Fin 2) :
  M.transitionOwner transition hinj (M.transitionEdge transition p) =
    Sum.inr p.1 := by
  classical
  have hpart : M.edgePartitionEquiv transition hinj
    (M.transitionEdge transition p) = Sum.inr p := by
    apply (M.edgePartitionEquiv transition hinj).symm.injective
    simp
  simp [transitionOwner, hpart]

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[transitionOwner_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma transitionOwner_left {T : Type*}
  (transition : T → M.EdgeTransition)
  (hinj : Function.Injective (M.transitionEdge transition)) (t : T) :
  M.transitionOwner transition hinj (transition t).left = Sum.inr t := by
  simpa [transitionEdge] using
    M.transitionOwner_transitionEdge transition hinj (t, (0 : Fin 2))

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[transitionOwner_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma transitionOwner_right {T : Type*}
  (transition : T → M.EdgeTransition)
  (hinj : Function.Injective (M.transitionEdge transition)) (t : T) :
  M.transitionOwner transition hinj (transition t).right = Sum.inr t := by
  simpa [transitionEdge] using
    M.transitionOwner_transitionEdge transition hinj (t, (1 : Fin 2))

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[transitionOwner_eq_inl_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma transitionOwner_eq_inl_iff {T : Type*}
  (transition : T → M.EdgeTransition)
  (hinj : Function.Injective (M.transitionEdge transition)) (e : E)
  (f : M.UnpairedTransitionEdge transition) :
  M.transitionOwner transition hinj e = Sum.inl f ↔ e = f.1 := by
  classical
  constructor
  · intro h
    generalize hp : M.edgePartitionEquiv transition hinj e = z at h
    cases z with
    | inl g =>
      simp only [transitionOwner, hp, Sum.inl.injEq] at h
      subst g
      apply (M.edgePartitionEquiv transition hinj).injective
      simpa using hp
    | inr p => simp [transitionOwner, hp] at h
  · rintro rfl
    exact M.transitionOwner_unpaired transition hinj f

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[transitionOwner_eq_inr_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma transitionOwner_eq_inr_iff {T : Type*}
  (transition : T → M.EdgeTransition)
  (hinj : Function.Injective (M.transitionEdge transition)) (e : E) (t : T) :
  M.transitionOwner transition hinj e = Sum.inr t ↔
    e = (transition t).left ∨ e = (transition t).right := by
  classical
  constructor
  · intro h
    generalize hp : M.edgePartitionEquiv transition hinj e = z at h
    cases z with
    | inl f => simp [transitionOwner, hp] at h
    | inr p =>
      simp only [transitionOwner, hp, Sum.inr.injEq] at h
      have he : e = M.transitionEdge transition p := by
        apply (M.edgePartitionEquiv transition hinj).injective
        simpa using hp
      have hside : p.2 = 0 ∨ p.2 = 1 := by
        have hval : p.2.val = 0 ∨ p.2.val = 1 := by omega
        exact hval.imp Fin.ext Fin.ext
      obtain hzero | hone := hside
      · left
        rw [he, show p = (t, 0) by ext <;> simp [h, hzero], transitionEdge]
        simp
      · right
        rw [he, show p = (t, 1) by ext <;> simp [h, hone], transitionEdge]
        simp
  · rintro (rfl | rfl)
    · exact M.transitionOwner_left transition hinj t
    · exact M.transitionOwner_right transition hinj t

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[mem_transitionExpansionEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma mem_transitionExpansionEdges_iff {T : Type*}
  (transition : T → M.EdgeTransition)
  (hinj : Function.Injective (M.transitionEdge transition)) (e : E)
  (f : M.CompressedTransitionEdge transition) :
  e ∈ M.transitionExpansionEdges transition f ↔
    M.transitionOwner transition hinj e = f := by
  cases f with
  | inl f =>
    simpa [transitionExpansionEdges] using
      (M.transitionOwner_eq_inl_iff transition hinj e f).symm
  | inr t =>
    simpa [transitionExpansionEdges] using
      (M.transitionOwner_eq_inr_iff transition hinj e t).symm

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[mem_expandTransitions_edges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
walk. -/
private lemma mem_expandTransitions_edges_iff [DecidableEq V] {T : Type*}
  (transition : T → M.EdgeTransition)
  (hinj : Function.Injective (M.transitionEdge transition)) {u v : V}
  (p : (M.compressTransitions transition).IndexedWalk u v) (e : E) :
  e ∈ (M.expandTransitions transition p).edges ↔
    M.transitionOwner transition hinj e ∈ p.edges := by
  rw [(M.expandTransitions_edges_perm transition p).mem_iff, List.mem_flatMap]
  constructor
  · rintro ⟨f, hf, he⟩
    rw [M.mem_transitionExpansionEdges_iff transition hinj e f] at he
    rwa [he]
  · intro he
    exact ⟨M.transitionOwner transition hinj e, he,
      (M.mem_transitionExpansionEdges_iff transition hinj e _).mpr rfl⟩

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[transitionExpansionEdges_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma transitionExpansionEdges_nodup {T : Type*}
  (transition : T → M.EdgeTransition)
  (hinj : Function.Injective (M.transitionEdge transition))
  (f : M.CompressedTransitionEdge transition) :
  (M.transitionExpansionEdges transition f).Nodup := by
  cases f with
  | inl e => simp [transitionExpansionEdges]
  | inr t =>
    simp only [transitionExpansionEdges, List.nodup_cons, List.mem_singleton,
      List.not_mem_nil, not_false_eq_true]
    refine ⟨?_, by simp⟩
    intro h
    have hpairs : (t, (0 : Fin 2)) = (t, (1 : Fin 2)) := by
      apply hinj
      simpa [transitionEdge] using h
    exact Fin.zero_ne_one (congrArg Prod.snd hpairs)

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[flatMap_transitionExpansionEdges_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma flatMap_transitionExpansionEdges_nodup {T : Type*}
  (transition : T → M.EdgeTransition)
  (hinj : Function.Injective (M.transitionEdge transition))
  (l : List (M.CompressedTransitionEdge transition)) (hl : l.Nodup) :
  (l.flatMap (M.transitionExpansionEdges transition)).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun f _ ↦ M.transitionExpansionEdges_nodup transition hinj f, ?_⟩
  apply hl.imp
  intro f g hfg
  rw [Function.onFun, List.disjoint_left]
  intro e hef heg
  have hf := (M.mem_transitionExpansionEdges_iff transition hinj e f).mp hef
  have hg := (M.mem_transitionExpansionEdges_iff transition hinj e g).mp heg
  exact hfg (hf.symm.trans hg)

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[expandTransitions_isEulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma expandTransitions_isEulerian [DecidableEq V] {T : Type*}
  (transition : T → M.EdgeTransition)
  (hinj : Function.Injective (M.transitionEdge transition)) {u : V}
  (p : (M.compressTransitions transition).IndexedWalk u u)
  (hp : p.IsEulerian) : (M.expandTransitions transition p).IsEulerian := by
  constructor
  · apply (M.expandTransitions_edges_perm transition p).nodup_iff.mpr
    exact M.flatMap_transitionExpansionEdges_nodup transition hinj p.edges hp.1
  · intro e
    apply (M.mem_expandTransitions_edges_iff transition hinj p e).mpr
    exact hp.2 (M.transitionOwner transition hinj e)
/-! ## ParallelPairDeletion -/
namespace SimpleGraph
namespace EdgeIndexedMultigraph

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[edge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma ParallelPair.edge_injective {M : EdgeIndexedMultigraph V E}
  (p : M.ParallelPair) :
  Function.Injective p.edge := by
  intro i j hij
  have hi : i = 0 ∨ i = 1 := by
    have hval : i.val = 0 ∨ i.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  have hj : j = 0 ∨ j = 1 := by
    have hval : j.val = 0 ∨ j.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  obtain rfl | rfl <;> rcases hj with rfl | rfl := hi
  · rfl
  · exact False.elim (p.ne (by simpa [ParallelPair.edge] using hij))
  · exact False.elim (p.ne (by simpa [ParallelPair.edge] using hij.symm))
  · rfl

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[liftTransition_edge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma ParallelPair.liftTransition_edge_injective
  {M : EdgeIndexedMultigraph V E} {T : Type*} (p : M.ParallelPair)
  (transition : T → M.EdgeTransition)
  (hleft : ∀ t, (transition t).left ∉ Set.range p.edge)
  (hright : ∀ t, (transition t).right ∉ Set.range p.edge)
  (hinj : Function.Injective (M.transitionEdge transition)) :
  Function.Injective ((M.eraseParallelPair p).transitionEdge
    (fun t ↦ p.liftTransition (transition t) (hleft t) (hright t))) := by
  intro a b hab
  apply hinj
  obtain ⟨a, side⟩ := a
  obtain ⟨b, side'⟩ := b
  have hside : side = 0 ∨ side = 1 := by
    have hval : side.val = 0 ∨ side.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  have hside' : side' = 0 ∨ side' = 1 := by
    have hval : side'.val = 0 ∨ side'.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  obtain rfl | rfl <;> rcases hside' with rfl | rfl := hside
  all_goals
    have hval := congrArg Subtype.val hab
    simpa [transitionEdge, ParallelPair.liftTransition] using hval

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[parallelPairPartition_symm_apply_inl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma parallelPairPartition_symm_apply_inl (p : M.ParallelPair)
  (e : M.ErasedParallelPair p) :
  (M.parallelPairPartition p).symm (Sum.inl e) = e.1 := by
  simp [parallelPairPartition]

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[parallelPairPartition_symm_apply_inr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma parallelPairPartition_symm_apply_inr (p : M.ParallelPair)
  (i : Fin 2) :
  (M.parallelPairPartition p).symm (Sum.inr i) = p.edge i := by
  simp [parallelPairPartition]

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[eraseParallelPair_degree_eq_of_not_inc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma eraseParallelPair_degree_eq_of_not_inc [Finite E]
  (p : M.ParallelPair) (v : V) (hfirst : ¬M.Inc v p.first) :
  (M.eraseParallelPair p).degree v = M.degree v := by
  classical
  have hsecond : ¬M.Inc v p.second := by
    intro h
    apply hfirst
    rw [Inc] at h ⊢
    rwa [p.ends_eq]
  let f : {e : M.ErasedParallelPair p // (M.eraseParallelPair p).Inc v e} ≃
    {e : E // M.Inc v e} := {
    toFun := fun e ↦ ⟨e.1.1, e.2⟩
    invFun := fun e ↦ ⟨⟨e.1, by
      rw [p.mem_range_edge_iff]
      push Not
      exact ⟨fun h ↦ hfirst (h ▸ e.2), fun h ↦ hsecond (h ▸ e.2)⟩⟩, e.2⟩
    left_inv := by intro e; rfl
    right_inv := by intro e; rfl }
  rw [degree, degree]
  exact Set.ncard_congr' f

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[eraseParallelPair_even_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma eraseParallelPair_even_degree [Finite E] (p : M.ParallelPair)
  (heven : ∀ v, Even (M.degree v)) (v : V) :
  Even ((M.eraseParallelPair p).degree v) := by
  classical
  let _ := Fintype.ofFinite E
  apply ZMod.natCast_eq_zero_iff_even.mp
  have hpair : M.incidenceWeight v p.first = M.incidenceWeight v p.second := by
    unfold incidenceWeight Inc
    rw [p.ends_eq]
  have hpair_zero : ∑ i : Fin 2, M.incidenceWeight v (p.edge i) = 0 := by
    rw [Fin.sum_univ_two]
    change M.incidenceWeight v p.first + M.incidenceWeight v p.second = 0
    rw [hpair]
    unfold incidenceWeight
    split
    · change ((2 : ℕ) : ZMod 2) = 0
      exact ZMod.natCast_eq_zero_iff_even.mpr even_two
    · simp
  have hpartition : (∑ e : E, M.incidenceWeight v e) =
    (∑ e : M.ErasedParallelPair p, M.incidenceWeight v e.1) +
      ∑ i : Fin 2, M.incidenceWeight v (p.edge i) := by
    calc
      (∑ e : E, M.incidenceWeight v e) =
        ∑ z : M.ErasedParallelPair p ⊕ Fin 2,
          M.incidenceWeight v ((M.parallelPairPartition p).symm z) :=
        ((M.parallelPairPartition p).symm.sum_comp (M.incidenceWeight v)).symm
      _ = (∑ e : M.ErasedParallelPair p, M.incidenceWeight v e.1) +
        ∑ i : Fin 2, M.incidenceWeight v (p.edge i) := by
        rw [Fintype.sum_sum_type]
        simp
  calc
    ((M.eraseParallelPair p).degree v : ZMod 2) =
      ∑ e : M.ErasedParallelPair p, M.incidenceWeight v e.1 := by
      rw [(M.eraseParallelPair p).degree_cast_eq_sum_incidence]
      rfl
    _ = (∑ e : M.ErasedParallelPair p, M.incidenceWeight v e.1) + 0 := by simp
    _ = (∑ e : M.ErasedParallelPair p, M.incidenceWeight v e.1) +
      ∑ i : Fin 2, M.incidenceWeight v (p.edge i) := by rw [hpair_zero]
    _ = ∑ e : E, M.incidenceWeight v e := hpartition.symm
    _ = (M.degree v : ZMod 2) := (M.degree_cast_eq_sum_incidence v).symm
    _ = 0 := ZMod.natCast_eq_zero_iff_even.mpr (heven v)
/-! ## CycleForcedTransitions -/
namespace SimpleGraph
namespace Walk
universe u

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[augmentedTrailMultigraph_ends_original](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma augmentedTrailMultigraph_ends_original (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (i : Fin c.length) :
  (c.augmentedTrailMultigraph cover q).ends
    (c.augmentedOriginalEdge cover q i) =
    s(c.getVert i, c.getVert (i + 1)) :=
  rfl

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[augmentedTrailMultigraph_ends_copy](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma augmentedTrailMultigraph_ends_copy (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  {i : Fin c.length} (hi : q.copies i = 1) :
  (c.augmentedTrailMultigraph cover q).ends
    (c.augmentedCopiedEdge cover q hi) =
    s(c.getVert i, c.getVert (i.val + 1)) :=
  rfl

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[augmentedTrailMultigraph_ends_cover](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma augmentedTrailMultigraph_ends_cover (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (D : c.outsideGraph.ConnectedComponent) (e : (cover D).Edge) :
  (c.augmentedTrailMultigraph cover q).ends (c.augmentedCoverEdge cover q D e) =
    (cover D).multigraph.ends e :=
  rfl

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutAugmentedTrailMultigraph_ends_original](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutAugmentedTrailMultigraph_ends_original (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (j : Fin c.length) (hj : j ≠ cut.1) :
  (c.cutAugmentedTrailMultigraph cover q cut).ends
    (c.cutOriginalEdge cover q cut j hj) =
    s(c.getVert j, c.getVert (j + 1)) :=
  c.augmentedTrailMultigraph_ends_original cover q j

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutAugmentedTrailMultigraph_ends_copy](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutAugmentedTrailMultigraph_ends_copy (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (i : UncutActiveCycleCopy q cut) :
  (c.cutAugmentedTrailMultigraph cover q cut).ends
    (c.cutCopiedEdge cover q cut i) =
    s(c.getVert i.1.1, c.getVert (i.1.1.val + 1)) :=
  c.augmentedTrailMultigraph_ends_copy cover q i.1.2

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutAugmentedTrailMultigraph_ends_cover](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutAugmentedTrailMultigraph_ends_cover (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (D : c.outsideGraph.ConnectedComponent)
  (e : (cover D).Edge) :
  (c.cutAugmentedTrailMultigraph cover q cut).ends
    (c.cutCoverEdge cover q cut D e) =
    (cover D).multigraph.ends e :=
  c.augmentedTrailMultigraph_ends_cover cover q D e

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma ActiveCycleCopy.ne_zero {n : ℕ} [NeZero n]
  {d : Fin n → ℕ} (q : CyclicParityCompletion d) (i : ActiveCycleCopy q) :
  i.1 ≠ 0 := by
  intro hi
  have hone := i.2
  rw [hi, q.copies_zero] at hone
  omega

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[ne_of_copies_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma ActiveCycleCopy.ne_of_copies_eq_zero {n : ℕ} [NeZero n]
  {d : Fin n → ℕ} (q : CyclicParityCompletion d) (i : ActiveCycleCopy q)
  (j : Fin n) (hj : q.copies j = 0) : i.1 ≠ j := by
  intro hij
  subst j
  omega

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[val_add_one_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma ActiveCycleCopy.val_add_one_lt {n : ℕ} [NeZero n]
  {d : Fin n → ℕ} (q : CyclicParityCompletion d) (i : ActiveCycleCopy q)
  (hlast : q.copies (cycleLastIndex n) = 0) : i.1.val + 1 < n := by
  have hn : 0 < n := NeZero.pos n
  have hilast : i.1 ≠ cycleLastIndex n :=
    i.ne_of_copies_eq_zero q _ hlast
  have hilastval : i.1.val ≠ n - 1 := by
    intro h
    apply hilast
    apply Fin.ext
    exact h
  have hi := i.1.isLt
  omega

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[forwardLastCutCycleTransition_before](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma forwardLastCutCycleTransition_before (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (hlast : q.copies (cycleLastIndex c.length) = 1)
  (i : UncutActiveCycleCopy q (lastActiveCycleCopy q hlast)) :
  (c.forwardLastCutCycleTransition hc cover q hlast i).before =
    c.getVert (i.1.1.val - 1) :=
  rfl

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[forwardLastCutCycleTransition_after](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma forwardLastCutCycleTransition_after (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (hlast : q.copies (cycleLastIndex c.length) = 1)
  (i : UncutActiveCycleCopy q (lastActiveCycleCopy q hlast)) :
  (c.forwardLastCutCycleTransition hc cover q hlast i).after =
    c.getVert (i.1.1.val + 1) :=
  rfl

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[forwardLastCutCycleTransition_center](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma forwardLastCutCycleTransition_center (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (hlast : q.copies (cycleLastIndex c.length) = 1)
  (i : UncutActiveCycleCopy q (lastActiveCycleCopy q hlast)) :
  (c.forwardLastCutCycleTransition hc cover q hlast i).center =
    c.getVert i.1.1 :=
  rfl

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[forwardLastCutCycleTransition_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma forwardLastCutCycleTransition_right (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (hlast : q.copies (cycleLastIndex c.length) = 1)
  (i : UncutActiveCycleCopy q (lastActiveCycleCopy q hlast)) :
  (c.forwardLastCutCycleTransition hc cover q hlast i).right =
    c.cutCopiedEdge cover q (lastActiveCycleCopy q hlast) i :=
  rfl

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[splitCycleTransition_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma splitCycleTransition_left (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (i : ActiveCycleCopy q) :
  (c.splitCycleTransition hc cover q k hlast i).left =
    c.augmentedOriginalEdge cover q (splitPartnerIndex k i.1) := by
  by_cases h : i.1.val < k.val <;> simp [splitCycleTransition, h]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[splitCycleTransition_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma splitCycleTransition_right (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (i : ActiveCycleCopy q) :
  (c.splitCycleTransition hc cover q k hlast i).right =
    c.augmentedCopiedEdge cover q i.2 := by
  by_cases h : i.1.val < k.val <;> simp [splitCycleTransition, h]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[splitCycleTransition_before_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma splitCycleTransition_before_of_lt (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (i : ActiveCycleCopy q) (hi : i.1.val < k.val) :
  (c.splitCycleTransition hc cover q k hlast i).before =
    c.getVert (i.1.val - 1) := by
  simp [splitCycleTransition, hi]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[splitCycleTransition_after_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma splitCycleTransition_after_of_lt (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (i : ActiveCycleCopy q) (hi : i.1.val < k.val) :
  (c.splitCycleTransition hc cover q k hlast i).after =
    c.getVert (i.1.val + 1) := by
  simp [splitCycleTransition, hi]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[splitCycleTransition_center_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma splitCycleTransition_center_of_lt (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (i : ActiveCycleCopy q) (hi : i.1.val < k.val) :
  (c.splitCycleTransition hc cover q k hlast i).center = c.getVert i.1 := by
  simp [splitCycleTransition, hi]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[splitCycleTransition_before_of_not_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma splitCycleTransition_before_of_not_lt (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (i : ActiveCycleCopy q) (hi : ¬i.1.val < k.val) :
  (c.splitCycleTransition hc cover q k hlast i).before =
    c.getVert (i.1.val + 2) := by
  simp [splitCycleTransition, hi]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[splitCycleTransition_after_of_not_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma splitCycleTransition_after_of_not_lt (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (i : ActiveCycleCopy q) (hi : ¬i.1.val < k.val) :
  (c.splitCycleTransition hc cover q k hlast i).after = c.getVert i.1.val := by
  simp [splitCycleTransition, hi]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[splitCycleTransition_center_of_not_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma splitCycleTransition_center_of_not_lt (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (i : ActiveCycleCopy q) (hi : ¬i.1.val < k.val) :
  (c.splitCycleTransition hc cover q k hlast i).center =
    c.getVert (i.1.val + 1) := by
  simp [splitCycleTransition, hi]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutSplitCycleTransition_before](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutSplitCycleTransition_before (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (i : UncutActiveCycleCopy q cut) :
  (c.cutSplitCycleTransition hc cover q cut hlast i).before =
    (c.splitCycleTransition hc cover q cut.1 hlast i.1).before :=
  rfl

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutSplitCycleTransition_after](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutSplitCycleTransition_after (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (i : UncutActiveCycleCopy q cut) :
  (c.cutSplitCycleTransition hc cover q cut hlast i).after =
    (c.splitCycleTransition hc cover q cut.1 hlast i.1).after :=
  rfl

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutSplitCycleTransition_center](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutSplitCycleTransition_center (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (i : UncutActiveCycleCopy q cut) :
  (c.cutSplitCycleTransition hc cover q cut hlast i).center =
    (c.splitCycleTransition hc cover q cut.1 hlast i.1).center :=
  rfl

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutSplitCycleTransition_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutSplitCycleTransition_right (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (i : UncutActiveCycleCopy q cut) :
  (c.cutSplitCycleTransition hc cover q cut hlast i).right =
    c.cutCopiedEdge cover q cut i := by
  apply Subtype.ext
  exact c.splitCycleTransition_right hc cover q cut.1 hlast i.1

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutSplitCycleTransition_edge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutSplitCycleTransition_edge_injective (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0) :
  Function.Injective ((c.cutAugmentedTrailMultigraph cover q cut).transitionEdge
    (c.cutSplitCycleTransition hc cover q cut hlast)) := by
  apply (c.cycleParallelPair cover q cut.2).liftTransition_edge_injective
  intro a b h
  change
    (c.augmentedTrailMultigraph cover q).transitionEdge
      (c.splitCycleTransition hc cover q cut.1 hlast) (a.1.1, a.2) =
      (c.augmentedTrailMultigraph cover q).transitionEdge
        (c.splitCycleTransition hc cover q cut.1 hlast) (b.1.1, b.2) at h
  have h' : (a.1.1, a.2) = (b.1.1, b.2) :=
    c.splitCycleTransition_edge_injective hc cover q cut.1 hlast h
  have hfst : a.1.1 = b.1.1 :=
    congrArg (fun z : ActiveCycleCopy q × Fin 2 ↦ z.1) h'
  have hsnd : a.2 = b.2 :=
    congrArg (fun z : ActiveCycleCopy q × Fin 2 ↦ z.2) h'
  exact Prod.ext (Subtype.ext hfst) hsnd
/-! ## ReplacedPath -/
namespace SimpleGraph

end SimpleGraph.Walk

namespace SimpleGraph

/--
[reachable_of_adj_or_skip](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
replaced by a skip over that vertex. -/
private lemma reachable_of_adj_or_skip {V : Type*} {G : SimpleGraph V}
  (v : ℕ → V) (m : ℕ) (selected : ℕ → Prop)
  (hterminal : ¬selected m)
  (hadj : ∀ i, i < m → ¬selected (i + 1) → G.Adj (v i) (v (i + 1)))
  (hskip : ∀ i, i + 2 ≤ m → selected (i + 1) → G.Adj (v i) (v (i + 2))) :
  ∀ i, i ≤ m → G.Reachable (v i) (v m) := by
  classical
  intro i hi
  have hbase : ∀ j, m ≤ j → j ≤ m → G.Reachable (v j) (v m) := by
    intro j hmj hjm
    have hj : j = m := by omega
    subst j
    exact ⟨Walk.nil⟩
  have hstep : ∀ k (hk : k < m),
    (∀ j, k + 1 ≤ j → j ≤ m → G.Reachable (v j) (v m)) →
      ∀ j, k ≤ j → j ≤ m → G.Reachable (v j) (v m) := by
    intro k hk ih j hkj hjm
    by_cases hjk : j = k
    · subst j
      by_cases hs : selected (k + 1)
      · have hk2 : k + 2 ≤ m := by
        by_contra h
        have hkm : k + 1 = m := by omega
        exact hterminal (hkm ▸ hs)
        exact (hskip k hk2 hs).reachable.trans (ih (k + 2) (by omega) hk2)
      · exact (hadj k hk hs).reachable.trans
        (ih (k + 1) (by omega) (by omega))
    · exact ih j (by omega) hjm
  exact Nat.decreasingInduction (motive := fun k hk ↦
    ∀ j, k ≤ j → j ≤ m → G.Reachable (v j) (v m)) hstep hbase hi i (le_refl i) hi
end SimpleGraph
/-! ## CycleTransitionConnectivity -/
namespace SimpleGraph
namespace Walk
universe u

end SimpleGraph

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[split_original_not_paired](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma split_original_not_paired (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (j : Fin c.length)
  (hj : ∀ i : ActiveCycleCopy q, splitPartnerIndex k i.1 ≠ j) :
  c.augmentedOriginalEdge cover q j ∉ Set.range
    ((c.augmentedTrailMultigraph cover q).transitionEdge
      (c.splitCycleTransition hc cover q k hlast)) := by
  rintro ⟨⟨i, side⟩, he⟩
  have hside : side = 0 ∨ side = 1 := by
    have hval : side.val = 0 ∨ side.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  obtain rfl | rfl := hside
  · apply hj i
    simpa [EdgeIndexedMultigraph.transitionEdge, augmentedOriginalEdge] using he
  · simp [EdgeIndexedMultigraph.transitionEdge, augmentedOriginalEdge,
    augmentedCopiedEdge] at he

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[split_compressed_adj_original](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma split_compressed_adj_original (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (j : Fin c.length)
  (hj : ∀ i : ActiveCycleCopy q, splitPartnerIndex k i.1 ≠ j) :
  (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
    (c.getVert j) (c.getVert (j + 1)) := by
  apply (c.splitCompressedMultigraph hc cover q k hlast).underlying_adj.mpr
  exact ⟨Sum.inl ⟨c.augmentedOriginalEdge cover q j,
    c.split_original_not_paired hc cover q k hlast j hj⟩,
    c.augmentedTrailMultigraph_ends_original cover q j⟩

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[split_compressed_adj_forward_skip](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma split_compressed_adj_forward_skip (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (i : ActiveCycleCopy q) (hi : i.1.val < k.val) :
  (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
    (c.getVert (i.1.val - 1)) (c.getVert (i.1.val + 1)) := by
  apply (c.splitCompressedMultigraph hc cover q k hlast).underlying_adj.mpr
  refine ⟨Sum.inr i, ?_⟩
  change s((c.splitCycleTransition hc cover q k hlast i).before,
    (c.splitCycleTransition hc cover q k hlast i).after) = _
  rw [c.splitCycleTransition_before_of_lt hc cover q k hlast i hi,
    c.splitCycleTransition_after_of_lt hc cover q k hlast i hi]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[split_compressed_adj_reverse_skip](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma split_compressed_adj_reverse_skip (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (i : ActiveCycleCopy q) (hi : ¬i.1.val < k.val) :
  (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
    (c.getVert (i.1.val + 2)) (c.getVert i.1.val) := by
  apply (c.splitCompressedMultigraph hc cover q k hlast).underlying_adj.mpr
  refine ⟨Sum.inr i, ?_⟩
  change s((c.splitCycleTransition hc cover q k hlast i).before,
    (c.splitCycleTransition hc cover q k hlast i).after) = _
  rw [c.splitCycleTransition_before_of_not_lt hc cover q k hlast i hi,
    c.splitCycleTransition_after_of_not_lt hc cover q k hlast i hi]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[split_cycle_reachable_root](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma split_cycle_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (v : V) (hv : v ∈ c.support) :
  (c.splitCompressedMultigraph hc cover q k hlast).underlying.Reachable v x := by
  let i := hc.finLengthEquivSupport.symm ⟨v, hv⟩
  have hvi : c.getVert i = v := by
    apply (hc.finLengthEquivSupport_apply i).symm.trans
    simpa only [i] using
      congrArg Subtype.val (hc.finLengthEquivSupport.apply_symm_apply ⟨v, hv⟩)
  rw [← hvi]
  by_cases hik : i.val ≤ k.val
  · exact c.split_forward_reachable_root hc cover q k hlast i.val hik
  · exact c.split_reverse_reachable_root hc cover q k hlast i.val
    (by omega) i.isLt

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[splitCompressedMultigraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma splitCompressedMultigraph_connected (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0) :
  (c.splitCompressedMultigraph hc cover q k hlast).underlying.Connected := by
  exact c.connected_of_cycle_reachable_and_component_covers cover
    (c.splitCompressedMultigraph hc cover q k hlast).underlying
    (c.split_cycle_reachable_root hc cover q k hlast)
    (c.splitCompressedCoverHom hc cover q k hlast) (by intros; rfl)

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[forwardLast_original_not_paired](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma forwardLast_original_not_paired (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (hlast : q.copies (cycleLastIndex c.length) = 1) (j : Fin c.length)
  (hjcut : j ≠ cycleLastIndex c.length)
  (hj : ∀ i : UncutActiveCycleCopy q (lastActiveCycleCopy q hlast),
    i.1.1 - 1 ≠ j) :
  c.cutOriginalEdge cover q (lastActiveCycleCopy q hlast) j (by
    simpa [lastActiveCycleCopy] using hjcut) ∉ Set.range
    ((c.cutAugmentedTrailMultigraph cover q
      (lastActiveCycleCopy q hlast)).transitionEdge
      (c.forwardLastCutCycleTransition hc cover q hlast)) := by
  rintro ⟨⟨i, side⟩, he⟩
  have hside : side = 0 ∨ side = 1 := by
    have hval : side.val = 0 ∨ side.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  obtain rfl | rfl := hside
  · apply hj i
    have hval := congrArg Subtype.val he
    simpa [EdgeIndexedMultigraph.transitionEdge, forwardLastCutCycleTransition,
      cutOriginalEdge, augmentedOriginalEdge] using hval
  · have hval := congrArg Subtype.val he
    simp [EdgeIndexedMultigraph.transitionEdge, forwardLastCutCycleTransition,
      cutOriginalEdge, cutCopiedEdge, augmentedOriginalEdge,
      augmentedCopiedEdge] at hval

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[forwardLast_compressed_adj_original](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma forwardLast_compressed_adj_original (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (hlast : q.copies (cycleLastIndex c.length) = 1) (j : Fin c.length)
  (hjcut : j ≠ cycleLastIndex c.length)
  (hj : ∀ i : UncutActiveCycleCopy q (lastActiveCycleCopy q hlast),
    i.1.1 - 1 ≠ j) :
  (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying.Adj
    (c.getVert j) (c.getVert (j + 1)) := by
  let cut := lastActiveCycleCopy q hlast
  have hjcut' : j ≠ cut.1 := by simpa [cut, lastActiveCycleCopy] using hjcut
  apply (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying_adj.mpr
  exact ⟨Sum.inl ⟨c.cutOriginalEdge cover q cut j hjcut',
    c.forwardLast_original_not_paired hc cover q hlast j hjcut hj⟩,
    c.cutAugmentedTrailMultigraph_ends_original cover q cut j hjcut'⟩

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[forwardLast_compressed_adj_skip](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma forwardLast_compressed_adj_skip (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (hlast : q.copies (cycleLastIndex c.length) = 1)
  (i : UncutActiveCycleCopy q (lastActiveCycleCopy q hlast)) :
  (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying.Adj
    (c.getVert (i.1.1.val - 1)) (c.getVert (i.1.1.val + 1)) := by
  apply (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying_adj.mpr
  refine ⟨Sum.inr i, ?_⟩
  change s((c.forwardLastCutCycleTransition hc cover q hlast i).before,
    (c.forwardLastCutCycleTransition hc cover q hlast i).after) = _
  rw [c.forwardLastCutCycleTransition_before hc cover q hlast i,
    c.forwardLastCutCycleTransition_after hc cover q hlast i]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[forwardLast_reachable_root](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma forwardLast_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (hlast : q.copies (cycleLastIndex c.length) = 1)
  (r : ℕ) (hr : r ≤ c.length - 1) :
  (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying.Reachable
    (c.getVert r) x := by
  let m := c.length - 1
  let selected : ℕ → Prop := fun t ↦
    ∃ ht : t < c.length, t < m ∧ q.copies ⟨t, ht⟩ = 1
  have hterminal : ¬selected m := by
    rintro ⟨hmlen, hmm, hcopy⟩
    omega
  have hadj : ∀ i, i < m → ¬selected (i + 1) →
    (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying.Adj
      (c.getVert i) (c.getVert (i + 1)) := by
    intro i him hnsel
    let j : Fin c.length := ⟨i, by dsimp [m] at him; omega⟩
    have hjcut : j ≠ cycleLastIndex c.length := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [j, cycleLastIndex, m] at hval him
      omega
    apply c.forwardLast_compressed_adj_original hc cover q hlast j hjcut
    intro a heq
    have hval := congrArg Fin.val heq
    have hapos : 0 < a.1.1.val :=
      Nat.pos_of_ne_zero (fun h ↦ a.1.ne_zero q (Fin.ext h))
    rw [Fin.val_sub_one_of_ne_zero (a.1.ne_zero q)] at hval
    dsimp [j] at hval
    have hauncut : a.1.1 ≠ cycleLastIndex c.length := by
      simpa [lastActiveCycleCopy] using a.2
    have halt : a.1.1.val < m := by
      have hne : a.1.1.val ≠ c.length - 1 := fun h ↦ hauncut (Fin.ext h)
      dsimp [m]
      omega
    have haveq : a.1.1.val = i + 1 := by omega
    apply hnsel
    have hi1len : i + 1 < c.length := by rw [← haveq]; exact a.1.1.isLt
    have hi1m : i + 1 < m := by rwa [← haveq]
    refine ⟨hi1len, hi1m, ?_⟩
    rwa [show (⟨i + 1, hi1len⟩ : Fin c.length) = a.1.1 by exact Fin.ext haveq.symm]
  have hskip : ∀ i, i + 2 ≤ m → selected (i + 1) →
    (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying.Adj
      (c.getVert i) (c.getVert (i + 2)) := by
    rintro i hi2 ⟨hi1len, hi1m, hcopy⟩
    let a : ActiveCycleCopy q := ⟨⟨i + 1, hi1len⟩, hcopy⟩
    have hane : a.1 ≠ (lastActiveCycleCopy q hlast).1 := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [a, lastActiveCycleCopy, cycleLastIndex, m] at hval hi1m
      omega
    let a' : UncutActiveCycleCopy q (lastActiveCycleCopy q hlast) := ⟨a, hane⟩
    have h := c.forwardLast_compressed_adj_skip hc cover q hlast a'
    change (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying.Adj
      (c.getVert ((i + 1) - 1)) (c.getVert ((i + 1) + 1)) at h
    convert h using 1
    all_goals congr 1
  have hpath := reachable_of_adj_or_skip
    (G := (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying)
    (fun i ↦ c.getVert i) m selected hterminal hadj hskip
  have hroot := hpath 0 (Nat.zero_le m)
  exact (hpath r hr).trans (by simpa using hroot.symm)

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[forwardLastCutCompressedMultigraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
connectedness. -/
private lemma forwardLastCutCompressedMultigraph_connected (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (hlast : q.copies (cycleLastIndex c.length) = 1) :
  (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying.Connected := by
  have hcycle : ∀ v, v ∈ c.support →
    (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying.Reachable v x := by
    intro v hv
    let i := hc.finLengthEquivSupport.symm ⟨v, hv⟩
    have hvi : c.getVert i = v := by
      apply (hc.finLengthEquivSupport_apply i).symm.trans
      simpa only [i] using
        congrArg Subtype.val (hc.finLengthEquivSupport.apply_symm_apply ⟨v, hv⟩)
    rw [← hvi]
    apply c.forwardLast_reachable_root hc cover q hlast i.val
    omega
  exact c.connected_of_cycle_reachable_and_component_covers cover
    (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying hcycle
    (c.forwardLastCompressedCoverHom hc cover q hlast) (by intros; rfl)

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutSplit_original_not_paired](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutSplit_original_not_paired (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (j : Fin c.length) (hjcut : j ≠ cut.1)
  (hj : ∀ i : UncutActiveCycleCopy q cut,
    splitPartnerIndex cut.1 i.1.1 ≠ j) :
  c.cutOriginalEdge cover q cut j hjcut ∉ Set.range
    ((c.cutAugmentedTrailMultigraph cover q cut).transitionEdge
      (c.cutSplitCycleTransition hc cover q cut hlast)) := by
  rintro ⟨⟨i, side⟩, he⟩
  have hside : side = 0 ∨ side = 1 := by
    have hval : side.val = 0 ∨ side.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  obtain rfl | rfl := hside
  · apply hj i
    have hval := congrArg Subtype.val he
    simpa [EdgeIndexedMultigraph.transitionEdge, cutSplitCycleTransition,
      EdgeIndexedMultigraph.ParallelPair.liftTransition, cutOriginalEdge,
      augmentedOriginalEdge] using hval
  · have hval := congrArg Subtype.val he
    simp [EdgeIndexedMultigraph.transitionEdge, cutSplitCycleTransition,
      EdgeIndexedMultigraph.ParallelPair.liftTransition, cutOriginalEdge,
      augmentedOriginalEdge, augmentedCopiedEdge] at hval

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutSplit_compressed_adj_original](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutSplit_compressed_adj_original (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (j : Fin c.length) (hjcut : j ≠ cut.1)
  (hj : ∀ i : UncutActiveCycleCopy q cut,
    splitPartnerIndex cut.1 i.1.1 ≠ j) :
  (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
    (c.getVert j) (c.getVert (j + 1)) := by
  apply (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying_adj.mpr
  exact ⟨Sum.inl ⟨c.cutOriginalEdge cover q cut j hjcut,
    c.cutSplit_original_not_paired hc cover q cut hlast j hjcut hj⟩,
    c.cutAugmentedTrailMultigraph_ends_original cover q cut j hjcut⟩

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutSplit_compressed_adj_forward_skip](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutSplit_compressed_adj_forward_skip (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (i : UncutActiveCycleCopy q cut) (hi : i.1.1.val < cut.1.val) :
  (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
    (c.getVert (i.1.1.val - 1)) (c.getVert (i.1.1.val + 1)) := by
  apply (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying_adj.mpr
  refine ⟨Sum.inr i, ?_⟩
  change s((c.cutSplitCycleTransition hc cover q cut hlast i).before,
    (c.cutSplitCycleTransition hc cover q cut hlast i).after) = _
  rw [c.cutSplitCycleTransition_before, c.cutSplitCycleTransition_after,
    c.splitCycleTransition_before_of_lt hc cover q cut.1 hlast i.1 hi,
    c.splitCycleTransition_after_of_lt hc cover q cut.1 hlast i.1 hi]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutSplit_compressed_adj_reverse_skip](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutSplit_compressed_adj_reverse_skip (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (i : UncutActiveCycleCopy q cut) (hi : ¬i.1.1.val < cut.1.val) :
  (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
    (c.getVert (i.1.1.val + 2)) (c.getVert i.1.1.val) := by
  apply (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying_adj.mpr
  refine ⟨Sum.inr i, ?_⟩
  change s((c.cutSplitCycleTransition hc cover q cut hlast i).before,
    (c.cutSplitCycleTransition hc cover q cut hlast i).after) = _
  rw [c.cutSplitCycleTransition_before, c.cutSplitCycleTransition_after,
    c.splitCycleTransition_before_of_not_lt hc cover q cut.1 hlast i.1 hi,
    c.splitCycleTransition_after_of_not_lt hc cover q cut.1 hlast i.1 hi]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutSplit_cycle_reachable_root](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutSplit_cycle_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (v : V) (hv : v ∈ c.support) :
  (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Reachable v x := by
  let i := hc.finLengthEquivSupport.symm ⟨v, hv⟩
  have hvi : c.getVert i = v := by
    apply (hc.finLengthEquivSupport_apply i).symm.trans
    simpa only [i] using
      congrArg Subtype.val (hc.finLengthEquivSupport.apply_symm_apply ⟨v, hv⟩)
  rw [← hvi]
  by_cases hicut : i.val ≤ cut.1.val
  · exact c.cutSplit_forward_reachable_root hc cover q cut hlast i.val hicut
  · exact c.cutSplit_reverse_reachable_root hc cover q cut hlast i.val
    (by omega) i.isLt

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutSplitCompressedMultigraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
transitions preserves connectedness. -/
private lemma cutSplitCompressedMultigraph_connected (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0) :
  (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Connected := by
  exact c.connected_of_cycle_reachable_and_component_covers cover
    (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying
    (c.cutSplit_cycle_reachable_root hc cover q cut hlast)
    (c.cutSplitCompressedCoverHom hc cover q cut hlast) (by intros; rfl)
/-! ## CyclePreparedEuler -/
namespace SimpleGraph
namespace Walk
universe u

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[exists_split_compressed_eulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma exists_split_compressed_eulerian [Finite V] (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] (k : Fin c.length)
  (hlast : (c.cycleEulerizationCompletion hc cover).copies
    (cycleLastIndex c.length) = 0) :
  let q := c.cycleEulerizationCompletion hc cover
  let M := c.augmentedTrailMultigraph cover q
  let transition := c.splitCycleTransition hc cover q k hlast
  ∃ (u : V) (p : (M.compressTransitions transition).IndexedWalk u u),
    p.IsEulerian := by
  classical
  dsimp only
  let q := c.cycleEulerizationCompletion hc cover
  let M := c.augmentedTrailMultigraph cover q
  let transition := c.splitCycleTransition hc cover q k hlast
  have hinj : Function.Injective (M.transitionEdge transition) :=
    c.splitCycleTransition_edge_injective hc cover q k hlast
  have heven : ∀ v, Even ((M.compressTransitions transition).degree v) := by
    intro v
    apply M.compressTransitions_even_degree transition hinj
    exact c.cycleEulerization_even_degree hc cover
  exact (M.compressTransitions transition).exists_indexedEulerian
    (c.splitCompressedMultigraph_connected hc cover q k hlast) heven

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[exists_forwardLastCut_compressed_eulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma exists_forwardLastCut_compressed_eulerian [Finite V]
  (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length]
  (hlast : (c.cycleEulerizationCompletion hc cover).copies
    (cycleLastIndex c.length) = 1) :
  let q := c.cycleEulerizationCompletion hc cover
  let cut := lastActiveCycleCopy q hlast
  let M := c.cutAugmentedTrailMultigraph cover q cut
  let transition := c.forwardLastCutCycleTransition hc cover q hlast
  ∃ (u : V) (p : (M.compressTransitions transition).IndexedWalk u u),
    p.IsEulerian := by
  classical
  dsimp only
  let q := c.cycleEulerizationCompletion hc cover
  let cut := lastActiveCycleCopy q hlast
  let M := c.cutAugmentedTrailMultigraph cover q cut
  let transition := c.forwardLastCutCycleTransition hc cover q hlast
  have hbase : ∀ v, Even (M.degree v) := by
    intro v
    apply (c.augmentedTrailMultigraph cover q).eraseParallelPair_even_degree
      (c.cycleParallelPair cover q cut.2)
    exact c.cycleEulerization_even_degree hc cover
  have hinj : Function.Injective (M.transitionEdge transition) :=
    c.forwardLastCutCycleTransition_edge_injective hc cover q hlast
  have heven : ∀ v, Even ((M.compressTransitions transition).degree v) := by
    intro v
    exact M.compressTransitions_even_degree transition hinj hbase v
  exact (M.compressTransitions transition).exists_indexedEulerian
    (c.forwardLastCutCompressedMultigraph_connected hc cover q hlast) heven

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[exists_cutSplit_compressed_eulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma exists_cutSplit_compressed_eulerian [Finite V] (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length]
  (cut : ActiveCycleCopy (c.cycleEulerizationCompletion hc cover))
  (hlast : (c.cycleEulerizationCompletion hc cover).copies
    (cycleLastIndex c.length) = 0) :
  let q := c.cycleEulerizationCompletion hc cover
  let M := c.cutAugmentedTrailMultigraph cover q cut
  let transition := c.cutSplitCycleTransition hc cover q cut hlast
  ∃ (u : V) (p : (M.compressTransitions transition).IndexedWalk u u),
    p.IsEulerian := by
  classical
  dsimp only
  let q := c.cycleEulerizationCompletion hc cover
  let M := c.cutAugmentedTrailMultigraph cover q cut
  let transition := c.cutSplitCycleTransition hc cover q cut hlast
  have hbase : ∀ v, Even (M.degree v) := by
    intro v
    apply (c.augmentedTrailMultigraph cover q).eraseParallelPair_even_degree
      (c.cycleParallelPair cover q cut.2)
    exact c.cycleEulerization_even_degree hc cover
  have hinj : Function.Injective (M.transitionEdge transition) :=
    c.cutSplitCycleTransition_edge_injective hc cover q cut hlast
  have heven : ∀ v, Even ((M.compressTransitions transition).degree v) := by
    intro v
    exact M.compressTransitions_even_degree transition hinj hbase v
  exact (M.compressTransitions transition).exists_indexedEulerian
    (c.cutSplitCompressedMultigraph_connected hc cover q cut hlast) heven
/-! ## IndexedEulerCircuit -/
namespace SimpleGraph
namespace EdgeIndexedMultigraph
universe u v

end SimpleGraph.Walk

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
/--
[cyclicNext_prev](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cyclicNext_prev (n : ℕ) (hn : 0 < n) (i : Fin n) :
  cyclicNext n hn (cyclicPrev n hn i) = i := by
  apply Fin.ext
  by_cases h : i.val = 0
  · simp only [cyclicNext, cyclicPrev, Fin.val_mk]
    have hin : (i.val + n - 1) % n = n - 1 := by
      rw [h, zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [hin, show n - 1 + 1 = n by omega, Nat.mod_self, h]
  · simp only [cyclicNext, cyclicPrev, Fin.val_mk]
    have hin : (i.val + n - 1) % n = i.val - 1 := by
      rw [show i.val + n - 1 = (i.val - 1) + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [hin, Nat.sub_add_cancel (Nat.pos_of_ne_zero h), Nat.mod_eq_of_lt i.isLt]

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
/--
[cyclicPrev_next](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cyclicPrev_next (n : ℕ) (hn : 0 < n) (i : Fin n) :
  cyclicPrev n hn (cyclicNext n hn i) = i := by
  apply Fin.ext
  by_cases hlast : i.val + 1 = n
  · simp only [cyclicNext, cyclicPrev, Fin.val_mk]
    rw [hlast, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hlt : i.val + 1 < n := by omega
    simp only [cyclicNext, cyclicPrev, Fin.val_mk]
    rw [Nat.mod_eq_of_lt hlt,
      show i.val + 1 + n - 1 = i.val + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt i.isLt]

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
/--
[cyclicPrev_ne_next](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cyclicPrev_ne_next (n : ℕ) (hn : 0 < n) (hthree : 3 ≤ n)
  (i : Fin n) : cyclicPrev n hn i ≠ cyclicNext n hn i := by
  let _ : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hnext (j : Fin n) : cyclicNext n hn j = j + 1 := by
    apply Fin.ext
    simp [cyclicNext, Fin.val_add, Nat.mod_eq_of_lt (show 1 < n by omega)]
  intro h
  have htwo : i = cyclicNext n hn (cyclicNext n hn i) := by
    rw [← h, cyclicNext_prev]
  rw [hnext, hnext, add_assoc] at htwo
  have hcancel : i + 0 = i + ((1 : Fin n) + 1) := by simpa using htwo
  have hzero : (0 : Fin n) = (1 : Fin n) + 1 := add_left_cancel hcancel
  have hval := congrArg Fin.val hzero
  simp [Fin.val_add, Nat.mod_eq_of_lt (show 2 < n by omega)] at hval

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
/--
[cyclicPrev_val_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cyclicPrev_val_of_ne_zero (n : ℕ) (hn : 0 < n)
  (i : Fin n) (hi : i.val ≠ 0) : (cyclicPrev n hn i).val = i.val - 1 := by
  simp only [cyclicPrev, Fin.val_mk]
  rw [show i.val + n - 1 = (i.val - 1) + n by
    have hpos : 0 < i.val := Nat.pos_of_ne_zero hi
    omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[rotatedPositions_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma rotatedPositions_nodup (start : Fin C.size) :
  (C.rotatedPositions M start).Nodup := by
  rw [rotatedPositions, List.nodup_ofFn]
  intro i j hij
  let _ : NeZero C.size := ⟨Nat.ne_of_gt C.size_pos⟩
  apply add_left_cancel (a := start)
  exact hij

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[mem_rotatedPositions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma mem_rotatedPositions (start i : Fin C.size) :
  i ∈ C.rotatedPositions M start := by
  rw [rotatedPositions, List.mem_ofFn]
  let _ : NeZero C.size := ⟨Nat.ne_of_gt C.size_pos⟩
  exact ⟨(Equiv.addLeft start).symm i, (Equiv.addLeft start).apply_symm_apply i⟩

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[rotatedPosition_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma rotatedPosition_succ (start : Fin C.size) (i : ℕ)
  (hi : i + 1 < C.size) :
  C.rotatedPosition M start ⟨i + 1, hi⟩ =
    cyclicNext C.size C.size_pos
      (C.rotatedPosition M start ⟨i, by omega⟩) := by
  apply Fin.ext
  simp only [rotatedPosition, cyclicNext, Fin.val_mk, Fin.val_add]
  rw [Nat.mod_add_mod]
  congr 1

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[cyclicNext_rotatedPosition_last](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cyclicNext_rotatedPosition_last (start : Fin C.size) :
  cyclicNext C.size C.size_pos
    (C.rotatedPosition M start
      ⟨C.size - 1, by have := C.size_pos; omega⟩) = start := by
  apply Fin.ext
  simp only [rotatedPosition, cyclicNext, Fin.val_mk, Fin.val_add]
  rw [Nat.mod_add_mod,
    show start.val + (C.size - 1) + 1 = start.val + C.size by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt start.isLt]

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[closedRotatedPosition_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma closedRotatedPosition_succ (start : Fin C.size) (i : ℕ)
  (hi : i < C.size) :
  C.closedRotatedPosition M start ⟨i + 1, by omega⟩ =
    cyclicNext C.size C.size_pos
      (C.closedRotatedPosition M start ⟨i, by omega⟩) := by
  by_cases hnext : i + 1 < C.size
  · simp only [closedRotatedPosition, dite_eq_left hi, dite_eq_left hnext]
    exact C.rotatedPosition_succ M start i hnext
  · have hilast : i = C.size - 1 := by omega
    simp only [closedRotatedPosition, dite_eq_left hi, dite_eq_right hnext]
    subst i
    exact (C.cyclicNext_rotatedPosition_last M start).symm

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[markedVertexListing_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma markedVertexListing_eq (start : Fin C.size)
  (marked : Fin C.size → Bool) :
  C.markedVertexListing M start marked =
    (C.rotatedPositions M start).map
      (fun i ↦ (C.vertex i, marked i)) ++
    [(C.vertex start, marked start)] := by
  rw [markedVertexListing, List.ofFn_succ', List.concat_eq_append,
    rotatedPositions, List.map_ofFn]
  congr 1
  · rw [List.ofFn_inj]
    funext i
    simp [closedRotatedPosition]
  · simp [closedRotatedPosition]

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[markedVertexListing_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma markedVertexListing_isChain (start : Fin C.size)
  (marked : Fin C.size → Bool) (R : (V × Bool) → (V × Bool) → Prop)
  (hstep : ∀ i,
    R (C.vertex i, marked i)
      (C.vertex (cyclicNext C.size C.size_pos i),
        marked (cyclicNext C.size C.size_pos i))) :
  (C.markedVertexListing M start marked).IsChain R := by
  rw [markedVertexListing, List.isChain_ofFn]
  intro i hi
  have hi0 : i < C.size := by omega
  by_cases hnext : i + 1 < C.size
  · simp only [closedRotatedPosition, dite_eq_left hi0, dite_eq_left hnext]
    rw [C.rotatedPosition_succ M start i hnext]
    exact hstep _
  · have hilast : i = C.size - 1 := by omega
    simp only [closedRotatedPosition, dite_eq_left hi0, dite_eq_right hnext]
    have hpos : C.rotatedPosition M start ⟨i, hi0⟩ =
      C.rotatedPosition M start
        ⟨C.size - 1, by have := C.size_pos; omega⟩ := by
      congr
    rw [hpos]
    simpa only [C.cyclicNext_rotatedPosition_last M start] using
      hstep (C.rotatedPosition M start
        ⟨C.size - 1, by have := C.size_pos; omega⟩)

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[keptCoreVertices_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma keptCoreVertices_nodup (start : Fin C.size)
  (marked : Fin C.size → Bool)
  (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false) :
  (C.keptCoreVertices M start marked).Nodup := by
  rw [keptCoreVertices]
  apply C.rotatedPositions_nodup M start |>.filterMap
  intro i j z hzi hzj
  cases hi : marked i with
  | true => simp [keptVertex, hi] at hzi
  | false =>
    cases hj : marked j with
    | true => simp [keptVertex, hj] at hzj
    | false =>
      have hvi : C.vertex i = z := by simpa [keptVertex, hi] using hzi
      have hvj : C.vertex j = z := by simpa [keptVertex, hj] using hzj
      exact (hunique z).unique ⟨hvi, hi⟩ ⟨hvj, hj⟩

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[mem_keptCoreVertices](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma mem_keptCoreVertices (start : Fin C.size)
  (marked : Fin C.size → Bool)
  (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false) (z : V) :
  z ∈ C.keptCoreVertices M start marked := by
  obtain ⟨i, hi, _⟩ := hunique z
  rw [keptCoreVertices, List.mem_filterMap]
  exact ⟨i, C.mem_rotatedPositions M start i, by simp [keptVertex, hi]⟩

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[keptVertexListing_eq_root_next](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma keptVertexListing_eq_root_next (start : Fin C.size)
  (marked : Fin C.size → Bool) (hsize : 2 ≤ C.size)
  (hstart : marked start = false)
  (hnext : marked (cyclicNext C.size C.size_pos start) = false) :
  ∃ l, C.keptVertexListing M start marked =
    C.vertex start :: C.vertex (cyclicNext C.size C.size_pos start) ::
      l ++ [C.vertex start] := by
  obtain ⟨l, hl⟩ := C.rotatedPositions_eq_cons_cons M start hsize
  refine ⟨l.filterMap (C.keptVertex M marked), ?_⟩
  rw [keptVertexListing, keptCoreVertices, hl]
  simp [keptVertex, hstart, hnext]

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[getLast_rotatedPositions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma getLast_rotatedPositions (start : Fin C.size) :
  (C.rotatedPositions M start).getLast (by
    intro h
    have hlength := congrArg List.length h
    have hzero : C.size = 0 := by simpa [rotatedPositions] using hlength
    exact Nat.ne_of_gt C.size_pos hzero) =
    cyclicPrev C.size C.size_pos start :=
  have hfn : (List.ofFn fun i ↦ C.rotatedPosition M start i) ≠ [] := by
    intro h
    have hlength := congrArg List.length h
    have hzero : C.size = 0 := by simpa using hlength
    exact Nat.ne_of_gt C.size_pos hzero
  have hlast : (C.rotatedPositions M start).getLast (by
    simpa only [rotatedPositions] using hfn) =
    C.rotatedPosition M start
      ⟨C.size - 1, by have := C.size_pos; omega⟩ := by
    simpa only [rotatedPositions] using List.getLast_ofFn hfn
  rw [hlast]
  have hnext := C.cyclicNext_rotatedPosition_last M start
  have hprev := congrArg (cyclicPrev C.size C.size_pos) hnext
  rwa [cyclicPrev_next] at hprev

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[keptVertexListing_eq_prev_root](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma keptVertexListing_eq_prev_root (start : Fin C.size)
  (marked : Fin C.size → Bool) (hstart : marked start = false)
  (hprev : marked (cyclicPrev C.size C.size_pos start) = false) :
  ∃ l, C.keptVertexListing M start marked =
    l ++ [C.vertex (cyclicPrev C.size C.size_pos start), C.vertex start] := by
  have hrot : C.rotatedPositions M start ≠ [] := by
    intro h
    have hlength := congrArg List.length h
    have hzero : C.size = 0 := by simpa [rotatedPositions] using hlength
    exact Nat.ne_of_gt C.size_pos hzero
  have hcore : C.keptCoreVertices M start marked ≠ [] := by
    have hmem : C.vertex start ∈ C.keptCoreVertices M start marked := by
      rw [keptCoreVertices, List.mem_filterMap]
      exact ⟨start, C.mem_rotatedPositions M start start,
        by simp [keptVertex, hstart]⟩
    exact List.ne_nil_of_mem hmem
  have hlast : (C.keptCoreVertices M start marked).getLast hcore =
    C.vertex (cyclicPrev C.size C.size_pos start) := by
    change ((C.rotatedPositions M start).filterMap
      (C.keptVertex M marked)).getLast _ = _
    apply List.getLast_filterMap_of_eq_some hrot
    rw [C.getLast_rotatedPositions M start]
    simp [keptVertex, hprev]
  let core := C.keptCoreVertices M start marked
  have hdecomp : core.dropLast ++
    [C.vertex (cyclicPrev C.size C.size_pos start)] = core := by
    simpa only [core, hlast] using List.dropLast_append_getLast hcore
  refine ⟨core.dropLast, ?_⟩
  rw [keptVertexListing]
  calc
    C.keptCoreVertices M start marked ++ [C.vertex start] =
      (core.dropLast ++
        [C.vertex (cyclicPrev C.size C.size_pos start)]) ++
        [C.vertex start] := congrArg (· ++ [C.vertex start]) hdecomp.symm
    _ = core.dropLast ++
      [C.vertex (cyclicPrev C.size C.size_pos start), C.vertex start] := by simp

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[keptCoreVertices_eq_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma keptCoreVertices_eq_cons (start : Fin C.size)
  (marked : Fin C.size → Bool) (hstart : marked start = false)
  (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false) :
  ∃ l, C.keptCoreVertices M start marked = C.vertex start :: l := by
  have hrot : C.rotatedPositions M start ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    have hzero : C.size = 0 := by
      simpa only [rotatedPositions, List.length_ofFn, List.length_nil] using hlength
    exact Nat.ne_of_gt C.size_pos hzero
  have hrotHead : (C.rotatedPositions M start).head hrot = start := by
    have hfn : (List.ofFn fun i ↦ C.rotatedPosition M start i) ≠ [] := by
      simpa only [rotatedPositions] using hrot
    calc
      (C.rotatedPositions M start).head hrot =
        C.rotatedPosition M start ⟨0, C.size_pos⟩ := by
        simpa only [rotatedPositions] using List.head_ofFn hfn
      _ = start := by
        apply Fin.ext
        simp [rotatedPosition, Fin.val_add, Nat.mod_eq_of_lt start.isLt]
  have hcore : C.keptCoreVertices M start marked ≠ [] := by
    exact List.ne_nil_of_mem (C.mem_keptCoreVertices M start marked hunique (C.vertex start))
  obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil hcore
  have hhead : (C.keptCoreVertices M start marked).head hcore = C.vertex start := by
    change ((C.rotatedPositions M start).filterMap
      (C.keptVertex M marked)).head _ = C.vertex start
    apply List.head_filterMap_of_eq_some hrot
    rw [hrotHead]
    simp [keptVertex, hstart]
  have ha : a = C.vertex start := by
    simpa [hal] using hhead
  subst a
  exact ⟨l, hal⟩

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[keptVertexListing_tail_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma keptVertexListing_tail_nodup (start : Fin C.size)
  (marked : Fin C.size → Bool) (hstart : marked start = false)
  (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false) :
  (C.keptVertexListing M start marked).tail.Nodup := by
  obtain ⟨l, hl⟩ := C.keptCoreVertices_eq_cons M start marked hstart hunique
  have hn := C.keptCoreVertices_nodup M start marked hunique
  rw [keptVertexListing, hl, List.cons_append, List.tail_cons]
  rw [hl] at hn
  have hn' := List.nodup_cons.mp hn
  rw [List.nodup_append]
  refine ⟨hn'.2, List.nodup_singleton _, ?_⟩
  intro z hz z' hz'
  rw [List.mem_singleton] at hz'
  subst z'
  exact fun h ↦ hn'.1 (h ▸ hz)

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[ends_incoming](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma ends_incoming (i : Fin C.size) :
  M.ends (incoming M C i) =
    s(C.vertex (cyclicPrev C.size C.size_pos i), C.vertex i) := by
  rw [incoming, C.ends_edge, cyclicNext_prev]

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[existsUnique_keeps](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma existsUnique_keeps (anchor : V → E)
  (hinc : ∀ z, M.Inc z (anchor z)) (z : V) :
  ∃! i, C.vertex i = z ∧ Keeps M C anchor i := by
  classical
  have hatMost : ∀ i j,
    C.vertex i = z ∧ Keeps M C anchor i →
    C.vertex j = z ∧ Keeps M C anchor j → i = j := by
    intro i j hi hj
    obtain ⟨hiv, hiin | hiout⟩ := hi
    <;> rcases hj with ⟨hjv, hjin | hjout⟩
    · have hedge : cyclicPrev C.size C.size_pos i =
      cyclicPrev C.size C.size_pos j := by
      apply C.edge_bijective.1
      calc
        C.edge (cyclicPrev C.size C.size_pos i) = anchor (C.vertex i) := hiin
        _ = anchor (C.vertex j) := congrArg anchor (hiv.trans hjv.symm)
        _ = C.edge (cyclicPrev C.size C.size_pos j) := hjin.symm
      have := congrArg (cyclicNext C.size C.size_pos) hedge
      simpa using this
    · have hedge : cyclicPrev C.size C.size_pos i = j := by
      apply C.edge_bijective.1
      calc
        C.edge (cyclicPrev C.size C.size_pos i) = anchor (C.vertex i) := hiin
        _ = anchor (C.vertex j) := congrArg anchor (hiv.trans hjv.symm)
        _ = C.edge j := hjout.symm
      have hij : i = cyclicNext C.size C.size_pos j := by
        calc
          i = cyclicNext C.size C.size_pos
            (cyclicPrev C.size C.size_pos i) :=
            (cyclicNext_prev C.size C.size_pos i).symm
          _ = cyclicNext C.size C.size_pos j := congrArg _ hedge
      exfalso
      apply M.loopless (C.edge j) z
      rw [C.ends_edge, hjv, ← hij, hiv]
    · have hedge : i = cyclicPrev C.size C.size_pos j := by
      apply C.edge_bijective.1
      calc
        C.edge i = anchor (C.vertex i) := hiout
        _ = anchor (C.vertex j) := congrArg anchor (hiv.trans hjv.symm)
        _ = C.edge (cyclicPrev C.size C.size_pos j) := hjin.symm
      have hji : j = cyclicNext C.size C.size_pos i := by
        calc
          j = cyclicNext C.size C.size_pos
            (cyclicPrev C.size C.size_pos j) :=
            (cyclicNext_prev C.size C.size_pos j).symm
          _ = cyclicNext C.size C.size_pos i := congrArg _ hedge.symm
      exfalso
      apply M.loopless (C.edge i) z
      rw [C.ends_edge, hiv, ← hji, hjv]
    · apply C.edge_bijective.1
      exact hiout.trans ((congrArg anchor (hiv.trans hjv.symm)).trans hjout.symm)
  obtain ⟨j, hj⟩ := C.edge_bijective.2 (anchor z)
  have hzends : z ∈ s(C.vertex j,
    C.vertex (cyclicNext C.size C.size_pos j)) := by
    rw [← C.ends_edge, hj]
    exact hinc z
  obtain hzj | hznext := Sym2.mem_iff.mp hzends
  · refine ⟨j, ⟨hzj.symm, Or.inr ?_⟩, ?_⟩
    · simpa [hzj] using hj
    · intro i hi
      exact hatMost i j hi ⟨hzj.symm, Or.inr (by simpa [hzj] using hj)⟩
  · let i := cyclicNext C.size C.size_pos j
    have hiv : C.vertex i = z := hznext.symm
    have hiin : incoming M C i = anchor (C.vertex i) := by
      rw [incoming, cyclicPrev_next, hj, hiv]
    refine ⟨i, ⟨hiv, Or.inl hiin⟩, ?_⟩
    intro k hk
    exact hatMost k i hk ⟨hiv, Or.inl hiin⟩

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[existsUnique_anchorMarked](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma existsUnique_anchorMarked (anchor : V → E)
  (hinc : ∀ z, M.Inc z (anchor z)) (z : V) :
  ∃! i, C.vertex i = z ∧ anchorMarked M C anchor i = false := by
  classical
  simpa [anchorMarked] using C.existsUnique_keeps M anchor hinc z
/-! ## SquareShortcut marking -/
namespace SimpleGraph

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[keeps_of_degree_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma keeps_of_degree_eq_two (anchor : V → E)
  (hinc : ∀ z, M.Inc z (anchor z)) (i : Fin C.size)
  (hdegree : M.degree (C.vertex i) = 2) : C.Keeps M anchor i := by
  let incidence : Set E := {e | M.Inc (C.vertex i) e}
  have hincoming : C.incoming M i ∈ incidence := by
    simp [incidence, EdgeIndexedMultigraph.Inc]
  have houtgoing : C.edge i ∈ incidence := by
    simp [incidence, EdgeIndexedMultigraph.Inc, C.ends_edge]
  have hedges_ne : C.incoming M i ≠ C.edge i := by
    intro hedges
    have hpositions : cyclicPrev C.size C.size_pos i = i := by
      apply C.edge_bijective.1
      simpa only [incoming] using hedges
    have hnext : cyclicNext C.size C.size_pos i = i := by
      have h := congrArg (cyclicNext C.size C.size_pos) hpositions
      simpa using h.symm
    apply M.loopless (C.edge i) (C.vertex i)
    rw [C.ends_edge, hnext]
  have hincidence_card : incidence.ncard = 2 := by
    simpa [incidence, EdgeIndexedMultigraph.degree] using hdegree
  have hincidence_finite : incidence.Finite :=
    Set.finite_of_ncard_ne_zero (by omega)
  have hpair : ({C.incoming M i, C.edge i} : Set E) = incidence := by
    apply Set.eq_of_subset_of_ncard_le _ _ hincidence_finite
    · intro e he
      obtain rfl | he := Set.mem_insert_iff.mp he
      · exact hincoming
      · simpa using he ▸ houtgoing
    · rw [hincidence_card, Set.ncard_pair hedges_ne]
  have hanchor : anchor (C.vertex i) ∈ ({C.incoming M i, C.edge i} : Set E) := by
    rw [hpair]
    exact hinc (C.vertex i)
  obtain h | h := Set.mem_insert_iff.mp hanchor
  · exact Or.inl h.symm
  · exact Or.inr (Set.mem_singleton_iff.mp h).symm

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[anchorMarked_eq_false_of_degree_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma anchorMarked_eq_false_of_degree_eq_two (anchor : V → E)
  (hinc : ∀ z, M.Inc z (anchor z)) (i : Fin C.size)
  (hdegree : M.degree (C.vertex i) = 2) :
  C.anchorMarked M anchor i = false := by
  simp [anchorMarked, C.keeps_of_degree_eq_two M anchor hinc i hdegree]

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[noBacktrack_of_getElem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma noBacktrack_of_getElem (l : List (V × Bool))
  (hlocal : ∀ (i : ℕ) (hi : i + 2 < l.length),
    l[i + 1].2 = true → l[i].1 ≠ l[i + 2].1) :
  MarkedNoBacktrack l := by
  match l with
  | a :: b :: c :: t =>
    constructor
    · intro hb
      simpa using hlocal 0 (by simp) hb
    · apply noBacktrack_of_getElem (b :: c :: t)
      intro i hi hb
      have h := hlocal (i + 1) (by simpa using hi) hb
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  | [] => trivial
  | [_] => trivial
  | [_, _] => trivial
termination_by l.length

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[three_le_size_of_unique_unmarked](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma three_le_size_of_unique_unmarked [Fintype V]
  (marked : Fin C.size → Bool)
  (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false)
  (hcard : 3 ≤ Fintype.card V) : 3 ≤ C.size := by
  classical
  let position : V → Fin C.size := fun z ↦ Classical.choose (hunique z)
  have hposition (z : V) :
    C.vertex (position z) = z ∧ marked (position z) = false :=
    (Classical.choose_spec (hunique z)).1
  have hposition_injective : Function.Injective position := by
    intro z w hzw
    exact (hposition z).1.symm.trans
      ((congrArg C.vertex hzw).trans (hposition w).1)
  have hle : Fintype.card V ≤ Fintype.card (Fin C.size) :=
    Fintype.card_le_of_injective position hposition_injective
  simpa using hcard.trans hle

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[markedVertexListing_noBacktrack](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
pass, then no marked pass immediately backtracks. -/
private lemma markedVertexListing_noBacktrack [Fintype V]
  (start : Fin C.size) (marked : Fin C.size → Bool)
  (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false)
  (hedge : ∀ i, marked i = false ∨
    marked (cyclicNext C.size C.size_pos i) = false)
  (hcard : 3 ≤ Fintype.card V) :
  MarkedNoBacktrack (C.markedVertexListing M start marked) := by
  classical
  have hsize := C.three_le_size_of_unique_unmarked M marked hunique hcard
  have hpass (i : Fin C.size) (hi : marked i = true) :
    C.vertex (cyclicPrev C.size C.size_pos i) ≠
      C.vertex (cyclicNext C.size C.size_pos i) := by
    have hiprev : marked (cyclicPrev C.size C.size_pos i) = false := by
      obtain h | h := hedge (cyclicPrev C.size C.size_pos i)
      · exact h
      · rw [cyclicNext_prev] at h
        simp [hi] at h
    have hinext : marked (cyclicNext C.size C.size_pos i) = false := by
      obtain h | h := hedge i
      · simp [hi] at h
      · exact h
    intro heq
    have hpositions := (hunique
      (C.vertex (cyclicPrev C.size C.size_pos i))).unique
      ⟨rfl, hiprev⟩ ⟨heq.symm, hinext⟩
    exact cyclicPrev_ne_next C.size C.size_pos hsize i hpositions
  apply noBacktrack_of_getElem
  intro i hi hmarked
  have hlength :
    (C.markedVertexListing M start marked).length = C.size + 1 := by
    simp [markedVertexListing]
  have hi0 : i < C.size := by omega
  have hi1 : i + 1 < C.size := by omega
  let p0 := C.closedRotatedPosition M start ⟨i, by omega⟩
  let p1 := C.closedRotatedPosition M start ⟨i + 1, by omega⟩
  let p2 := C.closedRotatedPosition M start ⟨i + 2, by omega⟩
  have hp01 : p1 = cyclicNext C.size C.size_pos p0 :=
    C.closedRotatedPosition_succ M start i hi0
  have hp12 : p2 = cyclicNext C.size C.size_pos p1 := by
    simpa only [p1, p2, Nat.add_assoc, Nat.reduceAdd] using
      C.closedRotatedPosition_succ M start (i + 1) hi1
  have hp0 : p0 = cyclicPrev C.size C.size_pos p1 := by
    rw [hp01, cyclicPrev_next]
  have hmarked' : marked p1 = true := by
    simpa only [markedVertexListing, List.getElem_ofFn, p1] using hmarked
  have hne := hpass p1 hmarked'
  simpa only [markedVertexListing, List.getElem_ofFn, p0, p2, hp0, hp12] using hne

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[toHasStrongSquareCycle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma SquareMarking.toHasStrongSquareCycle
  [Fintype V] [DecidableEq V] {G : SimpleGraph V} {root : V}
  (K : C.SquareMarking M G root) : G.HasStrongSquareCycle root :=
  K.toStrongSquareCycleListing.toHasStrongSquareCycle
/-! ## CycleEulerMarking -/
namespace SimpleGraph
namespace Walk
universe u

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[exists_incident_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
off-cycle vertices have degree two. -/
private lemma IsCycle.exists_incident_anchor {E : Type*} {c : G.Walk x x}
  (hc : c.IsCycle) (M : EdgeIndexedMultigraph V E)
  (cycleAnchor : Fin c.length → E)
  (hcycleInc : ∀ i : Fin c.length, M.Inc (c.getVert i) (cycleAnchor i))
  (hdegree : ∀ v ∉ c.support, M.degree v = 2) :
  ∃ anchor : V → E, (∀ v, M.Inc v (anchor v)) ∧
    ∀ i : Fin c.length, anchor (c.getVert i) = cycleAnchor i := by
  classical
  have houtside (v : V) (hv : v ∉ c.support) : ∃ e, M.Inc v e := by
    let incidence : Set E := {e | M.Inc v e}
    have hcard : incidence.ncard = 2 := by
      simpa [incidence, EdgeIndexedMultigraph.degree] using hdegree v hv
    have hne : incidence.ncard ≠ 0 := by rw [hcard]; omega
    exact Set.nonempty_of_ncard_ne_zero hne
  let cycleIndex (v : V) (hv : v ∈ c.support) : Fin c.length :=
    hc.finLengthEquivSupport.symm ⟨v, hv⟩
  let anchor : V → E := fun v ↦
    if hv : v ∈ c.support then cycleAnchor (cycleIndex v hv)
    else Classical.choose (houtside v hv)
  refine ⟨anchor, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ c.support
    · have hindex : c.getVert (cycleIndex v hv) = v := by
      have heq := hc.finLengthEquivSupport.apply_symm_apply ⟨v, hv⟩
      have hval := congrArg Subtype.val heq
      rwa [hc.finLengthEquivSupport_apply] at hval
      simp only [anchor, dite_eq_left hv]
      have h := hcycleInc (cycleIndex v hv)
      simpa only [hindex] using h
    · simp only [anchor, dite_eq_right hv]
      exact Classical.choose_spec (houtside v hv)
  · intro i
    have hmem : c.getVert i ∈ c.support := c.getVert_mem_support i
    have hindex : cycleIndex (c.getVert i) hmem = i := by
      apply hc.finLengthEquivSupport.injective
      rw [hc.finLengthEquivSupport.apply_symm_apply]
      apply Subtype.ext
      exact (hc.finLengthEquivSupport_apply i).symm
    simp [anchor, hmem, hindex]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[augmentedTrailMultigraph_square_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma augmentedTrailMultigraph_square_adj
  (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (e : c.AugmentedTrailEdge cover q) :
  (c.augmentedTrailMultigraph cover q).ends e ∈ G.square.edgeSet := by
  cases e with
  | inl e => exact c.trailSystemMultigraph_square_adj cover e
  | inr e =>
    have hadj : G.Adj (c.getVert e.1) (c.getVert (e.1.val + 1)) :=
      c.adj_getVert_succ e.1.isLt
    exact G.square.mem_edgeSet.mpr ⟨G.ne_of_adj hadj, Or.inl hadj⟩

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[augmentedTrailMultigraph_cycle_edge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma augmentedTrailMultigraph_cycle_edge
  (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (e : c.AugmentedTrailEdge cover q) (a b : V)
  (he : (c.augmentedTrailMultigraph cover q).ends e = s(a, b))
  (hcycle : a ∈ c.support ∨ b ∈ c.support) : G.Adj a b := by
  cases e with
  | inl e => exact c.trailSystemMultigraph_cycle_edge cover e a b he hcycle
  | inr e =>
    apply G.mem_edgeSet.mp
    rw [← he]
    exact c.cycleCopyMultigraph_mem_edgeSet q e

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutAugmentedTrailMultigraph_square_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutAugmentedTrailMultigraph_square_adj
  (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (e : c.CutAugmentedTrailEdge cover q cut) :
  (c.cutAugmentedTrailMultigraph cover q cut).ends e ∈ G.square.edgeSet :=
  c.augmentedTrailMultigraph_square_adj cover q e.1

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutAugmentedTrailMultigraph_cycle_edge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutAugmentedTrailMultigraph_cycle_edge
  (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (e : c.CutAugmentedTrailEdge cover q cut)
  (a b : V)
  (he : (c.cutAugmentedTrailMultigraph cover q cut).ends e = s(a, b))
  (hcycle : a ∈ c.support ∨ b ∈ c.support) : G.Adj a b :=
  c.augmentedTrailMultigraph_cycle_edge cover q e.1 a b he hcycle

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[augmentedTrailMultigraph_degree_eq_two_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma augmentedTrailMultigraph_degree_eq_two_of_not_mem [Finite V]
  (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  {v : V} (hv : v ∉ c.support) :
  (c.augmentedTrailMultigraph cover q).degree v = 2 := by
  classical
  rw [augmentedTrailMultigraph, EdgeIndexedMultigraph.disjointSum_degree,
    c.trailSystemMultigraph_degree_eq_two cover hv,
    c.cycleCopyMultigraph_degree_eq_zero_of_not_mem hc q hv]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[augmentedTrailMultigraph_degree_eq_two_of_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
augmented degree is two. -/
private lemma augmentedTrailMultigraph_degree_eq_two_of_bound [Finite V]
  (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] (i : Fin c.length)
  (hbound : c.IsBoundVertex (c.getVert i))
  (hi : (c.cycleEulerizationCompletion hc cover).copies i = 0) :
  (c.cycleEulerizationMultigraph hc cover).degree (c.getVert i) = 2 := by
  classical
  let q := c.cycleEulerizationCompletion hc cover
  change q.copies i = 0 at hi
  have htrail :=
    c.trailSystemMultigraph_degree_eq_two_of_isBoundVertex hc cover i hbound
  have hprev : q.copies (i - 1) = 0 := by
    have heven : Even ((c.trailSystemMultigraph cover).degree (c.getVert i) +
      q.copies (i - 1) + q.copies i) := q.even_at i
    rw [htrail, hi] at heven
    obtain ⟨m, hm⟩ := heven
    have hlt := q.copies_lt_two (i - 1)
    omega
  rw [cycleEulerizationMultigraph, EdgeIndexedMultigraph.disjointSum_degree,
    htrail, c.cycleCopyMultigraph_degree_getVert hc, hprev, hi]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutAugmentedTrailMultigraph_degree_eq_two_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutAugmentedTrailMultigraph_degree_eq_two_of_not_mem [Finite V]
  (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) {v : V} (hv : v ∉ c.support) :
  (c.cutAugmentedTrailMultigraph cover q cut).degree v = 2 := by
  let M := c.augmentedTrailMultigraph cover q
  let pair := c.cycleParallelPair cover q cut.2
  have hnot : ¬M.Inc v pair.first := by
    intro h
    change v ∈ s(c.getVert cut.1, c.getVert (cut.1 + 1)) at h
    obtain h | h := Sym2.mem_iff.mp h
    · exact hv (h ▸ c.getVert_mem_support cut.1)
    · exact hv (h ▸ c.getVert_mem_support (cut.1 + 1))
  rw [cutAugmentedTrailMultigraph]
  exact (M.eraseParallelPair_degree_eq_of_not_inc pair v hnot).trans
    (c.augmentedTrailMultigraph_degree_eq_two_of_not_mem hc cover q hv)

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[splitCycleAnchor_inc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma splitCycleAnchor_inc (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k i : Fin c.length) :
  (c.augmentedTrailMultigraph cover q).Inc (c.getVert i)
    (c.splitCycleAnchor cover q k i) := by
  change c.getVert i ∈
    (c.augmentedTrailMultigraph cover q).ends
      (c.augmentedOriginalEdge cover q (splitCycleAnchorIndex k i))
  rw [c.augmentedTrailMultigraph_ends_original]
  rw [Sym2.mem_iff]
  by_cases hi : i = 0
  · simp [splitCycleAnchorIndex, hi]
  · by_cases hik : i.val ≤ k.val
    · right
      simp only [splitCycleAnchorIndex, hi, hik, ↓reduceIte]
      rw [Fin.val_sub_one_of_ne_zero hi]
      congr 1
      have hipos : 0 < i.val := Nat.pos_of_ne_zero (fun h ↦ hi (Fin.ext h))
      omega
    · left
      simp [splitCycleAnchorIndex, hi, hik]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[exists_splitCycleAnchor_eq_original](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
from the root. -/
private lemma exists_splitCycleAnchor_eq_original (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k j : Fin c.length) (hj : j ≠ k) :
  ∃ i : Fin c.length,
    i ≠ 0 ∧
    (c.augmentedTrailMultigraph cover q).Inc (c.getVert i)
      (c.augmentedOriginalEdge cover q j) ∧
    c.splitCycleAnchor cover q k i = c.augmentedOriginalEdge cover q j := by
  by_cases hlt : j.val < k.val
  · have hbound : j.val + 1 < c.length := lt_of_le_of_lt hlt k.isLt
    let i : Fin c.length := ⟨j.val + 1, hbound⟩
    have hi0 : i ≠ 0 := by
      intro h
      have hval := congrArg Fin.val h
      simp [i] at hval
    have hik : i.val ≤ k.val := by simp [i]; omega
    have hindex : splitCycleAnchorIndex k i = j := by
      apply Fin.ext
      rw [splitCycleAnchorIndex, ite_eq_right hi0, ite_eq_left hik,
        Fin.val_sub_one_of_ne_zero hi0]
      simp [i]
    refine ⟨i, hi0, ?_, ?_⟩
    · change c.getVert i ∈
      (c.augmentedTrailMultigraph cover q).ends
        (c.augmentedOriginalEdge cover q j)
      rw [c.augmentedTrailMultigraph_ends_original, Sym2.mem_iff]
      right
      simp [i]
    · simp only [splitCycleAnchor]
      rw [hindex]
  · have hgt : k.val < j.val := by
    have hneval : j.val ≠ k.val := fun h ↦ hj (Fin.ext h)
    omega
    have hj0 : j ≠ 0 := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_zero] at hval
      omega
    have hindex : splitCycleAnchorIndex k j = j := by
      simp [splitCycleAnchorIndex, hj0, show ¬j.val ≤ k.val by omega]
    refine ⟨j, hj0, ?_, ?_⟩
    · change c.getVert j ∈
      (c.augmentedTrailMultigraph cover q).ends
        (c.augmentedOriginalEdge cover q j)
      rw [c.augmentedTrailMultigraph_ends_original, Sym2.mem_iff]
      exact Or.inl rfl
    · simp only [splitCycleAnchor]
      rw [hindex]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutSplitCycleAnchor_inc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma cutSplitCycleAnchor_inc (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (i : Fin c.length) :
  (c.cutAugmentedTrailMultigraph cover q cut).Inc (c.getVert i)
    (c.cutSplitCycleAnchor cover q cut i) := by
  change c.getVert i ∈
    (c.cutAugmentedTrailMultigraph cover q cut).ends
      (c.cutOriginalEdge cover q cut (splitCycleAnchorIndex cut.1 i) _)
  rw [c.cutAugmentedTrailMultigraph_ends_original, Sym2.mem_iff]
  by_cases hi : i = 0
  · simp [splitCycleAnchorIndex, hi]
  · by_cases hik : i.val ≤ cut.1.val
    · right
      simp only [splitCycleAnchorIndex, hi, hik, ↓reduceIte]
      rw [Fin.val_sub_one_of_ne_zero hi]
      congr 1
      have hipos : 0 < i.val := Nat.pos_of_ne_zero (fun h ↦ hi (Fin.ext h))
      omega
    · left
      simp [splitCycleAnchorIndex, hi, hik]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[exists_cutSplitCycleAnchor_eq_original](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma exists_cutSplitCycleAnchor_eq_original (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (j : Fin c.length) (hj : j ≠ cut.1) :
  ∃ i : Fin c.length,
    i ≠ 0 ∧
    (c.cutAugmentedTrailMultigraph cover q cut).Inc (c.getVert i)
      (c.cutOriginalEdge cover q cut j hj) ∧
    c.cutSplitCycleAnchor cover q cut i =
      c.cutOriginalEdge cover q cut j hj := by
  by_cases hlt : j.val < cut.1.val
  · have hbound : j.val + 1 < c.length := lt_of_le_of_lt hlt cut.1.isLt
    let i : Fin c.length := ⟨j.val + 1, hbound⟩
    have hi0 : i ≠ 0 := by
      intro h
      have hval := congrArg Fin.val h
      simp [i] at hval
    have hik : i.val ≤ cut.1.val := by simp [i]; omega
    have hindex : splitCycleAnchorIndex cut.1 i = j := by
      apply Fin.ext
      rw [splitCycleAnchorIndex, ite_eq_right hi0, ite_eq_left hik,
        Fin.val_sub_one_of_ne_zero hi0]
      simp [i]
    refine ⟨i, hi0, ?_, ?_⟩
    · change c.getVert i ∈
      (c.cutAugmentedTrailMultigraph cover q cut).ends
        (c.cutOriginalEdge cover q cut j hj)
      rw [c.cutAugmentedTrailMultigraph_ends_original, Sym2.mem_iff]
      right
      simp [i]
    · apply Subtype.ext
      simp only [cutSplitCycleAnchor, cutOriginalEdge]
      rw [hindex]
  · have hgt : cut.1.val < j.val := by
    have hneval : j.val ≠ cut.1.val := fun h ↦ hj (Fin.ext h)
    omega
    have hj0 : j ≠ 0 := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_zero] at hval
      omega
    have hindex : splitCycleAnchorIndex cut.1 j = j := by
      simp [splitCycleAnchorIndex, hj0, show ¬j.val ≤ cut.1.val by omega]
    refine ⟨j, hj0, ?_, ?_⟩
    · change c.getVert j ∈
      (c.cutAugmentedTrailMultigraph cover q cut).ends
        (c.cutOriginalEdge cover q cut j hj)
      rw [c.cutAugmentedTrailMultigraph_ends_original, Sym2.mem_iff]
      exact Or.inl rfl
    · apply Subtype.ext
      simp only [cutSplitCycleAnchor, cutOriginalEdge]
      rw [hindex]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[augmentedCopiedEdge_not_inc_getVert_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma augmentedCopiedEdge_not_inc_getVert_zero (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (i : ActiveCycleCopy q) (hlast : i.1 ≠ cycleLastIndex c.length) :
  ¬(c.augmentedTrailMultigraph cover q).Inc (c.getVert 0)
    (c.augmentedCopiedEdge cover q i.2) := by
  intro hinc
  change c.getVert 0 ∈
    s(c.getVert i.1, c.getVert (i.1.val + 1)) at hinc
  rw [hc.getVert_succ_eq_add_one] at hinc
  obtain h | h := Sym2.mem_iff.mp hinc
  · have hi0 : (0 : Fin c.length) = i.1 := hc.getVert_injective_fin h
    exact i.ne_zero q hi0.symm
  · have hadd : i.1 + 1 = 0 := hc.getVert_injective_fin h.symm
    have hsub : i.1 = (0 : Fin c.length) - 1 := eq_sub_iff_add_eq.mpr hadd
    have hone : (0 : Fin c.length) - 1 = cycleLastIndex c.length := by
      apply Fin.ext
      rw [sub_eq_add_neg, zero_add, Fin.val_neg]
      have htwo : 1 < c.length := lt_of_lt_of_le (by omega) hc.three_le_length
      have hne : (1 : Fin c.length) ≠ 0 := by
        intro heq
        have hval := congrArg Fin.val heq
        simp [Nat.mod_eq_of_lt htwo] at hval
      simp [hne, cycleLastIndex, Nat.mod_eq_of_lt htwo]
    exact hlast (hsub.trans hone)

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutCopiedEdge_not_inc_getVert_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
of the cycle. -/
private lemma cutCopiedEdge_not_inc_getVert_zero (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q) (i : UncutActiveCycleCopy q cut)
  (hlast : i.1.1 ≠ cycleLastIndex c.length) :
  ¬(c.cutAugmentedTrailMultigraph cover q cut).Inc (c.getVert 0)
    (c.cutCopiedEdge cover q cut i) := by
  intro hinc
  change c.getVert 0 ∈
    s(c.getVert i.1.1, c.getVert (i.1.1.val + 1)) at hinc
  rw [hc.getVert_succ_eq_add_one] at hinc
  obtain h | h := Sym2.mem_iff.mp hinc
  · have hi0 : (0 : Fin c.length) = i.1.1 := hc.getVert_injective_fin h
    exact i.1.ne_zero q hi0.symm
  · have hadd : i.1.1 + 1 = 0 := hc.getVert_injective_fin h.symm
    have hsub : i.1.1 = (0 : Fin c.length) - 1 :=
      eq_sub_iff_add_eq.mpr hadd
    have hone : (0 : Fin c.length) - 1 = cycleLastIndex c.length := by
      apply Fin.ext
      rw [sub_eq_add_neg, zero_add, Fin.val_neg]
      have htwo : 1 < c.length := lt_of_lt_of_le (by omega) hc.three_le_length
      have hne : (1 : Fin c.length) ≠ 0 := by
        intro heq
        have hval := congrArg Fin.val heq
        simp [Nat.mod_eq_of_lt htwo] at hval
      simp [hne, cycleLastIndex, Nat.mod_eq_of_lt htwo]
    exact hlast (hsub.trans hone)

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[forwardLastCutCycleTransition_left_eq_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
the transition center. -/
private lemma forwardLastCutCycleTransition_left_eq_anchor [Finite V]
  (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length]
  (hlast : (c.cycleEulerizationCompletion hc cover).copies
    (cycleLastIndex c.length) = 1)
  (i : UncutActiveCycleCopy (c.cycleEulerizationCompletion hc cover)
    (lastActiveCycleCopy (c.cycleEulerizationCompletion hc cover) hlast)) :
  let q := c.cycleEulerizationCompletion hc cover
  let cut := lastActiveCycleCopy q hlast
  c.cutSplitCycleAnchor cover q cut i.1.1 =
    (c.forwardLastCutCycleTransition hc cover q hlast i).left := by
  classical
  dsimp only
  let q := c.cycleEulerizationCompletion hc cover
  let cut := lastActiveCycleCopy q hlast
  have hi0 := i.1.ne_zero q
  have hle : i.1.1.val ≤ cut.1.val := by
    change i.1.1.val ≤ c.length - 1
    omega
  have hindex : splitCycleAnchorIndex cut.1 i.1.1 = i.1.1 - 1 := by
    simp [splitCycleAnchorIndex, hi0, hle]
  apply Subtype.ext
  change c.augmentedOriginalEdge cover q (splitCycleAnchorIndex cut.1 i.1.1) =
    c.augmentedOriginalEdge cover q (i.1.1 - 1)
  rw [hindex]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[exists_splitCycleTransition_center_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
by its left edge when the distinguished edge has no copy. -/
private lemma exists_splitCycleTransition_center_anchor (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
  (hk : q.copies k = 0) (i : ActiveCycleCopy q) :
  let transition := c.splitCycleTransition hc cover q k hlast
  ∃ a : Fin c.length, (transition i).center = c.getVert a ∧
    c.splitCycleAnchor cover q k a = (transition i).left := by
  dsimp only
  by_cases hlt : i.1.val < k.val
  · refine ⟨i.1, ?_, ?_⟩
    · exact c.splitCycleTransition_center_of_lt hc cover q k hlast i hlt
    · have hi0 := i.ne_zero q
      have hindex : splitCycleAnchorIndex k i.1 = i.1 - 1 := by
        simp [splitCycleAnchorIndex, hi0, show i.1.val ≤ k.val by omega]
      change c.augmentedOriginalEdge cover q (splitCycleAnchorIndex k i.1) =
        (c.splitCycleTransition hc cover q k hlast i).left
      rw [c.splitCycleTransition_left, splitPartnerIndex,
        ite_eq_left hlt, hindex]
  · have hgt : k.val < i.1.val := by
    have hneval : i.1.val ≠ k.val := fun h ↦
      i.ne_of_copies_eq_zero q k hk (Fin.ext h)
    omega
    have hbound : i.1.val + 1 < c.length := i.val_add_one_lt q hlast
    let a : Fin c.length := ⟨i.1.val + 1, hbound⟩
    refine ⟨a, ?_, ?_⟩
    · exact c.splitCycleTransition_center_of_not_lt hc cover q k hlast i hlt
    · have ha0 : a ≠ 0 := by
      intro h
      have hval := congrArg Fin.val h
      simp [a] at hval
      have haK : ¬a.val ≤ k.val := by
        change ¬ i.1.val + 1 ≤ k.val
        omega
      have htwo : 1 < c.length := by omega
      have hone : (1 : Fin c.length).val = 1 := Nat.mod_eq_of_lt htwo
      have hadd : i.1.val + (1 : Fin c.length).val < c.length := by
        simpa only [hone] using hbound
      have hindex : splitCycleAnchorIndex k a = i.1 + 1 := by
        apply Fin.ext
        rw [Fin.val_add_eq_of_add_lt hadd, hone]
        simp [splitCycleAnchorIndex, ha0, haK, a]
      change c.augmentedOriginalEdge cover q (splitCycleAnchorIndex k a) =
        (c.splitCycleTransition hc cover q k hlast i).left
      rw [c.splitCycleTransition_left, splitPartnerIndex,
        ite_eq_right hlt, hindex]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[exists_cutSplitCycleTransition_center_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
center by its left edge. -/
private lemma exists_cutSplitCycleTransition_center_anchor [Finite V]
  (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length]
  (cut : ActiveCycleCopy (c.cycleEulerizationCompletion hc cover))
  (hlast : (c.cycleEulerizationCompletion hc cover).copies
    (cycleLastIndex c.length) = 0)
  (i : UncutActiveCycleCopy (c.cycleEulerizationCompletion hc cover) cut) :
  let q := c.cycleEulerizationCompletion hc cover
  let transition := c.cutSplitCycleTransition hc cover q cut hlast
  ∃ a : Fin c.length, (transition i).center = c.getVert a ∧
    c.cutSplitCycleAnchor cover q cut a = (transition i).left := by
  classical
  dsimp only
  let q := c.cycleEulerizationCompletion hc cover
  let transition := c.cutSplitCycleTransition hc cover q cut hlast
  by_cases hlt : i.1.1.val < cut.1.val
  · refine ⟨i.1.1, ?_, ?_⟩
    · rw [c.cutSplitCycleTransition_center,
      c.splitCycleTransition_center_of_lt hc cover q cut.1 hlast i.1 hlt]
    · have hi0 := i.1.ne_zero q
      have hindex : splitCycleAnchorIndex cut.1 i.1.1 = i.1.1 - 1 := by
        simp [splitCycleAnchorIndex, hi0, show i.1.1.val ≤ cut.1.val by omega]
      apply Subtype.ext
      change c.augmentedOriginalEdge cover q (splitCycleAnchorIndex cut.1 i.1.1) =
        (c.splitCycleTransition hc cover q cut.1 hlast i.1).left
      rw [c.splitCycleTransition_left, splitPartnerIndex, ite_eq_left hlt, hindex]
  · have hgt : cut.1.val < i.1.1.val := by
    have hneval : i.1.1.val ≠ cut.1.val := fun h ↦ i.2 (Fin.ext h)
    omega
    have hbound : i.1.1.val + 1 < c.length := i.1.val_add_one_lt q hlast
    let a : Fin c.length := ⟨i.1.1.val + 1, hbound⟩
    refine ⟨a, ?_, ?_⟩
    · rw [c.cutSplitCycleTransition_center,
      c.splitCycleTransition_center_of_not_lt hc cover q cut.1 hlast i.1 hlt]
    · have ha0 : a ≠ 0 := by
      intro h
      have hval := congrArg Fin.val h
      simp [a] at hval
      have haCut : ¬a.val ≤ cut.1.val := by
        change ¬ i.1.1.val + 1 ≤ cut.1.val
        omega
      have htwo : 1 < c.length := by omega
      have hone : (1 : Fin c.length).val = 1 := Nat.mod_eq_of_lt htwo
      have hadd : i.1.1.val + (1 : Fin c.length).val < c.length := by
        simpa only [hone] using hbound
      have hindex : splitCycleAnchorIndex cut.1 a = i.1.1 + 1 := by
        apply Fin.ext
        rw [Fin.val_add_eq_of_add_lt hadd, hone]
        simp [splitCycleAnchorIndex, ha0, haCut, a]
      apply Subtype.ext
      change c.augmentedOriginalEdge cover q (splitCycleAnchorIndex cut.1 a) =
        (c.splitCycleTransition hc cover q cut.1 hlast i.1).left
      rw [c.splitCycleTransition_left, splitPartnerIndex, ite_eq_right hlt, hindex]

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[cutRootEdge_other_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
edge or is an off-cycle degree-two vertex. -/
private lemma cutRootEdge_other_endpoint [Finite V] (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (cut : ActiveCycleCopy q)
  (anchor : V → c.CutAugmentedTrailEdge cover q cut)
  (hcycleAnchor : ∀ i : Fin c.length, anchor (c.getVert i) =
    c.cutSplitCycleAnchor cover q cut i)
  (hcopyLast : ∀ i : UncutActiveCycleCopy q cut,
    i.1.1 ≠ cycleLastIndex c.length)
  (e : c.CutAugmentedTrailEdge cover q cut)
  (hrootInc : (c.cutAugmentedTrailMultigraph cover q cut).Inc x e) :
  (∃ z, z ≠ x ∧
    (c.cutAugmentedTrailMultigraph cover q cut).Inc z e ∧ anchor z = e) ∨
  ∃ z, z ≠ x ∧
    (c.cutAugmentedTrailMultigraph cover q cut).Inc z e ∧
    (c.cutAugmentedTrailMultigraph cover q cut).degree z = 2 := by
  rcases c.cutAugmentedTrailEdge_cases cover q cut e with
    ⟨j, hj, rfl⟩ | ⟨D, f, rfl⟩ | ⟨i, rfl⟩
  · obtain ⟨a, ha0, hainc, haanchor⟩ :=
    c.exists_cutSplitCycleAnchor_eq_original cover q cut j hj
    left
    refine ⟨c.getVert a, ?_, hainc, ?_⟩
    · intro hax
      have ha : a = 0 := by
        apply hc.getVert_injective_fin
        exact hax.trans c.getVert_zero.symm
      exact ha0 ha
    · rw [hcycleAnchor a, haanchor]
  · obtain ⟨z, hzD, hzends⟩ := (cover D).meets_component f
    have hzout : z ∉ c.support := c.componentVertices_subset_compl D hzD
    right
    refine ⟨z, ?_, ?_, c.cutAugmentedTrailMultigraph_degree_eq_two_of_not_mem
      hc cover q cut hzout⟩
    · intro hzx
      apply hzout
      subst z
      simpa only [c.getVert_zero] using c.getVert_mem_support 0
    · exact hzends
  · exfalso
    apply c.cutCopiedEdge_not_inc_getVert_zero hc cover q cut i (hcopyLast i)
    simpa only [c.getVert_zero] using hrootInc

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[augmentedTrailEdge_cases](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
copied cycle edge. -/
private lemma augmentedTrailEdge_cases (c : G.Walk x x)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (e : c.AugmentedTrailEdge cover q) :
  (∃ j : Fin c.length, e = c.augmentedOriginalEdge cover q j) ∨
  (∃ (D : c.outsideGraph.ConnectedComponent) (f : (cover D).Edge),
    e = c.augmentedCoverEdge cover q D f) ∨
  ∃ i : ActiveCycleCopy q, e = c.augmentedCopiedEdge cover q i.2 := by
  cases e with
  | inl e =>
    cases e with
    | inl j => exact Or.inl ⟨j.down, rfl⟩
    | inr f => exact Or.inr (Or.inl ⟨f.1, f.2, rfl⟩)
  | inr f =>
    obtain ⟨j, r⟩ := f
    have hcopy : q.copies j = 1 := by
      have hpos : 0 < q.copies j := Nat.pos_of_ne_zero (by
        intro hzero
        simpa [hzero] using r.isLt)
      have hlt := q.copies_lt_two j
      omega
    let i : ActiveCycleCopy q := ⟨j, hcopy⟩
    right
    right
    refine ⟨i, ?_⟩
    apply congrArg Sum.inr
    dsimp only [i]
    congr 1
    apply Fin.ext
    omega

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[splitRootEdge_other_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
anchored or has degree two. -/
private lemma splitRootEdge_other_endpoint [Finite V] (c : G.Walk x x)
  (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
  (k : Fin c.length) (hk0 : k ≠ 0)
  (anchor : V → c.AugmentedTrailEdge cover q)
  (hcycleAnchor : ∀ i : Fin c.length, anchor (c.getVert i) =
    c.splitCycleAnchor cover q k i)
  (hdegreeK : (c.augmentedTrailMultigraph cover q).degree (c.getVert k) = 2)
  (hcopyLast : ∀ i : ActiveCycleCopy q,
    i.1 ≠ cycleLastIndex c.length)
  (e : c.AugmentedTrailEdge cover q)
  (hrootInc : (c.augmentedTrailMultigraph cover q).Inc x e) :
  (∃ z, z ≠ x ∧
    (c.augmentedTrailMultigraph cover q).Inc z e ∧ anchor z = e) ∨
  ∃ z, z ≠ x ∧
    (c.augmentedTrailMultigraph cover q).Inc z e ∧
    (c.augmentedTrailMultigraph cover q).degree z = 2 := by
  rcases c.augmentedTrailEdge_cases cover q e with
    ⟨j, rfl⟩ | ⟨D, f, rfl⟩ | ⟨i, rfl⟩
  · by_cases hj : j = k
    · subst j
      right
      refine ⟨c.getVert k, ?_, ?_, hdegreeK⟩
      · intro hyx
        have hk : k = 0 := by
          apply hc.getVert_injective_fin
          exact hyx.trans c.getVert_zero.symm
        exact hk0 hk
      · change c.getVert k ∈
        (c.augmentedTrailMultigraph cover q).ends
          (c.augmentedOriginalEdge cover q k)
        rw [c.augmentedTrailMultigraph_ends_original, Sym2.mem_iff]
        exact Or.inl rfl
    · obtain ⟨a, ha0, hainc, haanchor⟩ :=
      c.exists_splitCycleAnchor_eq_original cover q k j hj
      left
      refine ⟨c.getVert a, ?_, hainc, ?_⟩
      · intro hax
        have ha : a = 0 := by
          apply hc.getVert_injective_fin
          exact hax.trans c.getVert_zero.symm
        exact ha0 ha
      · rw [hcycleAnchor a, haanchor]
  · obtain ⟨z, hzD, hzends⟩ := (cover D).meets_component f
    have hzout : z ∉ c.support := c.componentVertices_subset_compl D hzD
    right
    refine ⟨z, ?_, ?_, c.augmentedTrailMultigraph_degree_eq_two_of_not_mem
      hc cover q hzout⟩
    · intro hzx
      apply hzout
      subst z
      simpa only [c.getVert_zero] using c.getVert_mem_support 0
    · exact hzends
  · exfalso
    apply c.augmentedCopiedEdge_not_inc_getVert_zero hc cover q i (hcopyLast i)
    simpa only [c.getVert_zero] using hrootInc

end SimpleGraph.Walk

namespace SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)
/--
[toCyclicCircuit_exists_pass_of_edgesAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
Euler-circuit encoding. -/
private lemma toCyclicCircuit_exists_pass_of_edgesAdjacent [Nonempty E]
  {u : V} (p : M.IndexedWalk u u) (hp : p.IsEulerian)
  (e f : E) (h : EdgesAdjacent e f p.edges) :
  let C := p.toCyclicCircuit M hp
  ∃ i, (C.incoming M i = e ∧ C.edge i = f) ∨
    (C.incoming M i = f ∧ C.edge i = e) := by
  classical
  let C := p.toCyclicCircuit M hp
  obtain ⟨before, after, h | h⟩ := h
  · have hlt : before.length + 1 < C.size := by
    change before.length + 1 < p.edges.length
    rw [h]
    simp
    let i : Fin C.size := ⟨before.length + 1, hlt⟩
    have hi : i.val ≠ 0 := by simp [i]
    have hincoming : C.incoming M i = e := by
      rw [CyclicCircuit.incoming, show cyclicPrev C.size C.size_pos i =
        ⟨before.length, by omega⟩ by
          apply Fin.ext
          rw [cyclicPrev_val_of_ne_zero C.size C.size_pos i hi]
          simp [i]]
      have hbound : before.length < p.edges.length := by rw [h]; simp
      change p.edges.get ⟨before.length, hbound⟩ = e
      have hget : p.edges[before.length]? = some e := by rw [h]; simp
      obtain ⟨_, hvalue⟩ := List.getElem?_eq_some_iff.mp hget
      simpa using hvalue
    have houtgoing : C.edge i = f := by
      have hbound : before.length + 1 < p.edges.length := by rw [h]; simp
      change p.edges.get ⟨before.length + 1, hbound⟩ = f
      have hget : p.edges[before.length + 1]? = some f := by rw [h]; simp
      obtain ⟨_, hvalue⟩ := List.getElem?_eq_some_iff.mp hget
      simpa using hvalue
    exact ⟨i, Or.inl ⟨hincoming, houtgoing⟩⟩
  · have hlt : before.length + 1 < C.size := by
    change before.length + 1 < p.edges.length
    rw [h]
    simp
    let i : Fin C.size := ⟨before.length + 1, hlt⟩
    have hi : i.val ≠ 0 := by simp [i]
    have hincoming : C.incoming M i = f := by
      rw [CyclicCircuit.incoming, show cyclicPrev C.size C.size_pos i =
        ⟨before.length, by omega⟩ by
          apply Fin.ext
          rw [cyclicPrev_val_of_ne_zero C.size C.size_pos i hi]
          simp [i]]
      have hbound : before.length < p.edges.length := by rw [h]; simp
      change p.edges.get ⟨before.length, hbound⟩ = f
      have hget : p.edges[before.length]? = some f := by rw [h]; simp
      obtain ⟨_, hvalue⟩ := List.getElem?_eq_some_iff.mp hget
      simpa using hvalue
    have houtgoing : C.edge i = e := by
      have hbound : before.length + 1 < p.edges.length := by rw [h]; simp
      change p.edges.get ⟨before.length + 1, hbound⟩ = e
      have hget : p.edges[before.length + 1]? = some e := by rw [h]; simp
      obtain ⟨_, hvalue⟩ := List.getElem?_eq_some_iff.mp hget
      simpa using hvalue
    exact ⟨i, Or.inr ⟨hincoming, houtgoing⟩⟩
namespace CyclicCircuit
universe u v

end SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[transition_eq_center_of_inc_left_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma transition_eq_center_of_inc_left_right
  (t : M.EdgeTransition) (z : V)
  (hleft : M.Inc z t.left) (hright : M.Inc z t.right) : z = t.center := by
  rw [EdgeIndexedMultigraph.Inc, t.left_ends] at hleft
  rw [EdgeIndexedMultigraph.Inc, t.right_ends] at hright
  obtain hleft | hleft <;> := Sym2.mem_iff.mp hleft
    obtain hright | hright := Sym2.mem_iff.mp hright
  · have hsame : t.before = t.center := hleft.symm.trans hright
    exact False.elim (M.loopless t.left t.center (by simpa [hsame] using t.left_ends))
  · exact False.elim (t.before_ne_after (hleft.symm.trans hright))
  · exact hleft
  · have hsame : t.center = t.after := hleft.symm.trans hright
    exact False.elim (M.loopless t.right t.center (by simpa [hsame] using t.right_ends))

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[transitionRight_has_unmarked_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
unmarked circuit endpoint. -/
private lemma transitionRight_has_unmarked_endpoint
  (anchor : V → E) (t : M.EdgeTransition)
  (hanchor : anchor t.center = t.left)
  (hpass : ∃ j, (C.incoming M j = t.left ∧ C.edge j = t.right) ∨
    (C.incoming M j = t.right ∧ C.edge j = t.left))
  (i : Fin C.size) (hi : C.edge i = t.right) :
  C.anchorMarked M anchor i = false ∨
    C.anchorMarked M anchor (cyclicNext C.size C.size_pos i) = false := by
  classical
  obtain ⟨j, hpass | hpass⟩ := hpass
  · have hjvertex : C.vertex j = t.center := by
    apply transition_eq_center_of_inc_left_right M t
    · rw [← hpass.1]
      simp [EdgeIndexedMultigraph.Inc]
    · rw [← hpass.2]
      rw [EdgeIndexedMultigraph.Inc, C.ends_edge]
      simp
    have hkeeps : C.Keeps M anchor j := by
      left
      exact hpass.1.trans ((congrArg anchor hjvertex).trans hanchor).symm
    have hfalse : C.anchorMarked M anchor j = false := by
      simp [CyclicCircuit.anchorMarked, hkeeps]
    left
    have hij : i = j := C.edge_bijective.1 (hi.trans hpass.2.symm)
    simpa [hij] using hfalse
  · have hjvertex : C.vertex j = t.center := by
    apply transition_eq_center_of_inc_left_right M t
    · rw [← hpass.2]
      rw [EdgeIndexedMultigraph.Inc, C.ends_edge]
      simp
    · rw [← hpass.1]
      simp [EdgeIndexedMultigraph.Inc]
    have hkeeps : C.Keeps M anchor j := by
      right
      exact hpass.2.trans ((congrArg anchor hjvertex).trans hanchor).symm
    have hfalse : C.anchorMarked M anchor j = false := by
      simp [CyclicCircuit.anchorMarked, hkeeps]
    right
    have hiprev : i = cyclicPrev C.size C.size_pos j := by
      apply C.edge_bijective.1
      exact hi.trans hpass.1.symm
    rwa [hiprev, cyclicNext_prev]

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[anchorEdge_has_unmarked_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma anchorEdge_has_unmarked_endpoint
  (anchor : V → E) (i : Fin C.size) (z : V)
  (hinc : M.Inc z (C.edge i)) (hanchor : anchor z = C.edge i) :
  C.anchorMarked M anchor i = false ∨
    C.anchorMarked M anchor (cyclicNext C.size C.size_pos i) = false := by
  classical
  rw [EdgeIndexedMultigraph.Inc, C.ends_edge] at hinc
  obtain h | h := Sym2.mem_iff.mp hinc
  · left
    have hkeeps : C.Keeps M anchor i := by
      right
      exact hanchor.symm.trans (congrArg anchor h)
    simp [CyclicCircuit.anchorMarked, hkeeps]
  · right
    have hkeeps : C.Keeps M anchor
      (cyclicNext C.size C.size_pos i) := by
      left
      rw [CyclicCircuit.incoming, cyclicPrev_next]
      exact hanchor.symm.trans (congrArg anchor h)
    simp [CyclicCircuit.anchorMarked, hkeeps]

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[degreeTwo_has_unmarked_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma degreeTwo_has_unmarked_endpoint
  (anchor : V → E) (hanchorInc : ∀ z, M.Inc z (anchor z))
  (i : Fin C.size) (z : V) (hinc : M.Inc z (C.edge i))
  (hdegree : M.degree z = 2) :
  C.anchorMarked M anchor i = false ∨
    C.anchorMarked M anchor (cyclicNext C.size C.size_pos i) = false := by
  rw [EdgeIndexedMultigraph.Inc, C.ends_edge] at hinc
  obtain h | h := Sym2.mem_iff.mp hinc
  · left
    apply C.anchorMarked_eq_false_of_degree_eq_two M anchor hanchorInc
    simpa [h] using hdegree
  · right
    apply C.anchorMarked_eq_false_of_degree_eq_two M anchor hanchorInc
    simpa [h] using hdegree

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[anchorEdge_next_unmarked](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma anchorEdge_next_unmarked
  (anchor : V → E) (start : Fin C.size) (root z : V)
  (hroot : C.vertex start = root) (hz : z ≠ root)
  (hinc : M.Inc z (C.edge start)) (hanchor : anchor z = C.edge start) :
  C.anchorMarked M anchor (cyclicNext C.size C.size_pos start) = false := by
  classical
  rw [EdgeIndexedMultigraph.Inc, C.ends_edge] at hinc
  obtain h | h := Sym2.mem_iff.mp hinc
  · exact False.elim (hz (h.trans hroot))
  · have hkeeps : C.Keeps M anchor
    (cyclicNext C.size C.size_pos start) := by
    left
    rw [CyclicCircuit.incoming, cyclicPrev_next]
    exact hanchor.symm.trans (congrArg anchor h)
    simp [CyclicCircuit.anchorMarked, hkeeps]

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[degreeTwo_next_unmarked](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma degreeTwo_next_unmarked
  (anchor : V → E) (hanchorInc : ∀ z, M.Inc z (anchor z))
  (start : Fin C.size) (root z : V) (hroot : C.vertex start = root)
  (hz : z ≠ root) (hinc : M.Inc z (C.edge start))
  (hdegree : M.degree z = 2) :
  C.anchorMarked M anchor (cyclicNext C.size C.size_pos start) = false := by
  rw [EdgeIndexedMultigraph.Inc, C.ends_edge] at hinc
  obtain h | h := Sym2.mem_iff.mp hinc
  · exact False.elim (hz (h.trans hroot))
  · apply C.anchorMarked_eq_false_of_degree_eq_two M anchor hanchorInc
    simpa [h] using hdegree

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[anchorEdge_prev_unmarked](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma anchorEdge_prev_unmarked
  (anchor : V → E) (start : Fin C.size) (root z : V)
  (hroot : C.vertex start = root) (hz : z ≠ root)
  (hinc : M.Inc z (C.incoming M start))
  (hanchor : anchor z = C.incoming M start) :
  C.anchorMarked M anchor (cyclicPrev C.size C.size_pos start) = false := by
  classical
  rw [EdgeIndexedMultigraph.Inc, C.ends_incoming] at hinc
  obtain h | h := Sym2.mem_iff.mp hinc
  · have hkeeps : C.Keeps M anchor
    (cyclicPrev C.size C.size_pos start) := by
    right
    exact hanchor.symm.trans (congrArg anchor h)
    simp [CyclicCircuit.anchorMarked, hkeeps]
  · exact False.elim (hz (h.trans hroot))

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[degreeTwo_prev_unmarked](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma degreeTwo_prev_unmarked
  (anchor : V → E) (hanchorInc : ∀ z, M.Inc z (anchor z))
  (start : Fin C.size) (root z : V) (hroot : C.vertex start = root)
  (hz : z ≠ root) (hinc : M.Inc z (C.incoming M start))
  (hdegree : M.degree z = 2) :
  C.anchorMarked M anchor (cyclicPrev C.size C.size_pos start) = false := by
  rw [EdgeIndexedMultigraph.Inc, C.ends_incoming] at hinc
  obtain h | h := Sym2.mem_iff.mp hinc
  · apply C.anchorMarked_eq_false_of_degree_eq_two M anchor hanchorInc
    simpa [h] using hdegree
  · exact False.elim (hz (h.trans hroot))

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)
/--
[anchorMarked_toHasStrongSquareCycle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
Hamiltonian cycle in the graph square. -/
private lemma anchorMarked_toHasStrongSquareCycle [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (root : V) (support : Set V) (anchor : V → E)
  (hinc : ∀ z, M.Inc z (anchor z))
  (hdegree : ∀ z ∉ support, M.degree z = 2)
  (hsquare : ∀ e, M.ends e ∈ G.square.edgeSet)
  (horiginal : ∀ e a b, M.ends e = s(a, b) →
    (a ∈ support ∨ b ∈ support) → G.Adj a b)
  (start : Fin C.size) (hroot : C.vertex start = root)
  (hstart : C.anchorMarked M anchor start = false)
  (hedge : ∀ i, C.anchorMarked M anchor i = false ∨
    C.anchorMarked M anchor (cyclicNext C.size C.size_pos i) = false)
  (hnext : C.anchorMarked M anchor
    (cyclicNext C.size C.size_pos start) = false)
  (hprev : C.anchorMarked M anchor
    (cyclicPrev C.size C.size_pos start) = false)
  (hrootSupport : root ∈ support) (hcard : 3 ≤ Fintype.card V) :
  G.HasStrongSquareCycle root := by
  classical
  let marked := C.anchorMarked M anchor
  have hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false :=
    C.existsUnique_anchorMarked M anchor hinc
  have hsquare' (i : Fin C.size) : G.square.Adj (C.vertex i)
    (C.vertex (cyclicNext C.size C.size_pos i)) := by
    apply G.square.mem_edgeSet.mp
    rw [← C.ends_edge]
    exact hsquare (C.edge i)
  have horiginal' (i : Fin C.size)
    (hi : marked i = true ∨
      marked (cyclicNext C.size C.size_pos i) = true) :
    G.Adj (C.vertex i)
      (C.vertex (cyclicNext C.size C.size_pos i)) := by
    apply horiginal (C.edge i) _ _ (C.ends_edge i)
    obtain hi | hi := hi
    · left
      by_contra houtside
      have hfalse := C.anchorMarked_eq_false_of_degree_eq_two M anchor hinc i
        (hdegree (C.vertex i) houtside)
      exact Bool.false_ne_true (hfalse.symm.trans hi)
    · right
      let j := cyclicNext C.size C.size_pos i
      by_contra houtside
      have hfalse := C.anchorMarked_eq_false_of_degree_eq_two M anchor hinc j
        (hdegree (C.vertex j) houtside)
      exact Bool.false_ne_true (hfalse.symm.trans hi)
  have hnextAdj : G.Adj root
    (C.vertex (cyclicNext C.size C.size_pos start)) := by
    rw [← hroot]
    apply horiginal (C.edge start) _ _ (C.ends_edge start)
    exact Or.inl (hroot ▸ hrootSupport)
  have hprevAdj : G.Adj
    (C.vertex (cyclicPrev C.size C.size_pos start)) root := by
    rw [← hroot]
    let i := cyclicPrev C.size C.size_pos start
    apply horiginal (C.edge i) _ _
    · simpa [i] using C.ends_edge i
    · exact Or.inr (hroot ▸ hrootSupport)
  exact (SquareMarking.ofLocal M C G root start marked hroot hstart hunique
    hedge hsquare' horiginal' hnext hprev hnextAdj hprevAdj hcard).toHasStrongSquareCycle
namespace Walk
universe u

end SimpleGraph.EdgeIndexedMultigraph.CyclicCircuit

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[hasStrongSquareCycle_of_split](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
square when the distinguished bound vertex has no outgoing copied edge. -/
private lemma hasStrongSquareCycle_of_split [Fintype V] [DecidableEq V]
  (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] (k : Fin c.length) (hk0 : k ≠ 0)
  (hbound : c.IsBoundVertex (c.getVert k))
  (hlast : (c.cycleEulerizationCompletion hc cover).copies
    (cycleLastIndex c.length) = 0)
  (hk : (c.cycleEulerizationCompletion hc cover).copies k = 0)
  (hcard : 3 ≤ Fintype.card V) : G.HasStrongSquareCycle x := by
  classical
  let q := c.cycleEulerizationCompletion hc cover
  let M := c.augmentedTrailMultigraph cover q
  let transition := c.splitCycleTransition hc cover q k hlast
  have hinj : Function.Injective (M.transitionEdge transition) :=
    c.splitCycleTransition_edge_injective hc cover q k hlast
  obtain ⟨u, p, hp⟩ := c.exists_split_compressed_eulerian hc cover k hlast
  let tour := M.expandTransitions transition p
  have htour : tour.IsEulerian :=
    M.expandTransitions_isEulerian transition hinj p hp
  let edge0 := c.augmentedOriginalEdge cover q 0
  let _ : Nonempty (c.AugmentedTrailEdge cover q) := ⟨edge0⟩
  let C := tour.toCyclicCircuit M htour
  let cycleAnchor := c.splitCycleAnchor cover q k
  have hcycleInc : ∀ i : Fin c.length, M.Inc (c.getVert i) (cycleAnchor i) :=
    c.splitCycleAnchor_inc cover q k
  have hdegree : ∀ z ∉ c.support, M.degree z = 2 := by
    intro z hz
    exact c.augmentedTrailMultigraph_degree_eq_two_of_not_mem hc cover q hz
  have hdegreeK : M.degree (c.getVert k) = 2 := by
    exact c.augmentedTrailMultigraph_degree_eq_two_of_bound hc cover k hbound hk
  obtain ⟨anchor, hanchorInc, hcycleAnchor⟩ :=
    hc.exists_incident_anchor M cycleAnchor hcycleInc hdegree
  obtain ⟨start, ⟨hstartVertex, hstart⟩, _⟩ :=
    C.existsUnique_anchorMarked M anchor hanchorInc x
  have hedge (pos : Fin C.size) :
    C.anchorMarked M anchor pos = false ∨
      C.anchorMarked M anchor
        (EdgeIndexedMultigraph.cyclicNext C.size C.size_pos pos) = false := by
    rcases c.augmentedTrailEdge_cases cover q (C.edge pos) with
      ⟨j, he⟩ | ⟨D, f, he⟩ | ⟨i, he⟩
    · by_cases hj : j = k
      · subst j
        apply C.degreeTwo_has_unmarked_endpoint M anchor hanchorInc pos
          (c.getVert k)
        · rw [he]
          change c.getVert k ∈
            M.ends (c.augmentedOriginalEdge cover q k)
          rw [c.augmentedTrailMultigraph_ends_original, Sym2.mem_iff]
          exact Or.inl rfl
        · exact hdegreeK
      · obtain ⟨a, _, hainc, haedge⟩ :=
        c.exists_splitCycleAnchor_eq_original cover q k j hj
        apply C.anchorEdge_has_unmarked_endpoint M anchor pos (c.getVert a)
        · simpa only [he] using hainc
        · rw [hcycleAnchor a]
          change c.splitCycleAnchor cover q k a = C.edge pos
          exact haedge.trans he.symm
    · obtain ⟨z, hzD, hzends⟩ := (cover D).meets_component f
      have hzout : z ∉ c.support := c.componentVertices_subset_compl D hzD
      apply C.degreeTwo_has_unmarked_endpoint M anchor hanchorInc pos z
      · rw [he]
        exact hzends
      · exact hdegree z hzout
    · have hadjacent := M.expandTransitions_edges_adjacent transition p i
      (hp.2 (Sum.inr i))
      have hpass := tour.toCyclicCircuit_exists_pass_of_edgesAdjacent M htour
        (transition i).left (transition i).right hadjacent
      obtain ⟨a, hcenter, hleft⟩ :=
        c.exists_splitCycleTransition_center_anchor hc cover q k hlast hk i
      apply C.transitionRight_has_unmarked_endpoint M anchor (transition i)
      · rw [hcenter, hcycleAnchor a]
        exact hleft
      · exact hpass
      · rw [c.splitCycleTransition_right]
        exact he
  have hcopyLast : ∀ i : ActiveCycleCopy q,
    i.1 ≠ cycleLastIndex c.length := by
    intro i
    exact i.ne_of_copies_eq_zero q _ hlast
  have hnext : C.anchorMarked M anchor
    (EdgeIndexedMultigraph.cyclicNext C.size C.size_pos start) = false := by
    have hrootInc : M.Inc x (C.edge start) := by
      rw [EdgeIndexedMultigraph.Inc, C.ends_edge, Sym2.mem_iff]
      exact Or.inl hstartVertex.symm
    rcases c.splitRootEdge_other_endpoint hc cover q k hk0 anchor hcycleAnchor
      hdegreeK hcopyLast (C.edge start) hrootInc with h | h
    · obtain ⟨z, hzx, hzinc, hzanchor⟩ := h
      exact C.anchorEdge_next_unmarked M anchor start x z hstartVertex hzx
        hzinc hzanchor
    · obtain ⟨z, hzx, hzinc, hzdegree⟩ := h
      exact C.degreeTwo_next_unmarked M anchor hanchorInc start x z
        hstartVertex hzx hzinc hzdegree
  have hprev : C.anchorMarked M anchor
    (EdgeIndexedMultigraph.cyclicPrev C.size C.size_pos start) = false := by
    have hrootInc : M.Inc x (C.incoming M start) := by
      rw [EdgeIndexedMultigraph.Inc, C.ends_incoming, Sym2.mem_iff]
      exact Or.inr hstartVertex.symm
    rcases c.splitRootEdge_other_endpoint hc cover q k hk0 anchor hcycleAnchor
      hdegreeK hcopyLast (C.incoming M start) hrootInc with h | h
    · obtain ⟨z, hzx, hzinc, hzanchor⟩ := h
      exact C.anchorEdge_prev_unmarked M anchor start x z hstartVertex hzx
        hzinc hzanchor
    · obtain ⟨z, hzx, hzinc, hzdegree⟩ := h
      exact C.degreeTwo_prev_unmarked M anchor hanchorInc start x z
        hstartVertex hzx hzinc hzdegree
  apply C.anchorMarked_toHasStrongSquareCycle M G x {z | z ∈ c.support}
    anchor hanchorInc
    hdegree (c.augmentedTrailMultigraph_square_adj cover q)
    (c.augmentedTrailMultigraph_cycle_edge cover q) start
    hstartVertex hstart hedge hnext hprev
  · change x ∈ c.support
    simpa only [c.getVert_zero] using c.getVert_mem_support 0
  · exact hcard

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[hasStrongSquareCycle_of_forwardLastCut](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
Hamiltonian cycle in the square. -/
private lemma hasStrongSquareCycle_of_forwardLastCut [Fintype V] [DecidableEq V]
  (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length]
  (hlast : (c.cycleEulerizationCompletion hc cover).copies
    (cycleLastIndex c.length) = 1)
  (hcard : 3 ≤ Fintype.card V) : G.HasStrongSquareCycle x := by
  classical
  let q := c.cycleEulerizationCompletion hc cover
  let cut := lastActiveCycleCopy q hlast
  let M := c.cutAugmentedTrailMultigraph cover q cut
  let transition := c.forwardLastCutCycleTransition hc cover q hlast
  have hinj : Function.Injective (M.transitionEdge transition) :=
    c.forwardLastCutCycleTransition_edge_injective hc cover q hlast
  obtain ⟨u, p, hp⟩ := c.exists_forwardLastCut_compressed_eulerian hc cover hlast
  let tour := M.expandTransitions transition p
  have htour : tour.IsEulerian :=
    M.expandTransitions_isEulerian transition hinj p hp
  have hzeroLast : (0 : Fin c.length) ≠ cut.1 := by
    intro h
    have hval := congrArg Fin.val h
    change 0 = c.length - 1 at hval
    have hthree := hc.three_le_length
    omega
  let edge0 := c.cutOriginalEdge cover q cut 0 hzeroLast
  let _ : Nonempty (c.CutAugmentedTrailEdge cover q cut) := ⟨edge0⟩
  let C := tour.toCyclicCircuit M htour
  let cycleAnchor := c.cutSplitCycleAnchor cover q cut
  have hcycleInc : ∀ i : Fin c.length, M.Inc (c.getVert i) (cycleAnchor i) :=
    c.cutSplitCycleAnchor_inc cover q cut
  have hdegree : ∀ z ∉ c.support, M.degree z = 2 := by
    intro z hz
    exact c.cutAugmentedTrailMultigraph_degree_eq_two_of_not_mem
      hc cover q cut hz
  obtain ⟨anchor, hanchorInc, hcycleAnchor⟩ :=
    hc.exists_incident_anchor M cycleAnchor hcycleInc hdegree
  obtain ⟨start, ⟨hstartVertex, hstart⟩, _⟩ :=
    C.existsUnique_anchorMarked M anchor hanchorInc x
  have hedge (pos : Fin C.size) :
    C.anchorMarked M anchor pos = false ∨
      C.anchorMarked M anchor
        (EdgeIndexedMultigraph.cyclicNext C.size C.size_pos pos) = false := by
    rcases c.cutAugmentedTrailEdge_cases cover q cut (C.edge pos) with
      ⟨j, hj, he⟩ | ⟨D, f, he⟩ | ⟨i, he⟩
    · obtain ⟨a, _, hainc, haedge⟩ :=
      c.exists_cutSplitCycleAnchor_eq_original cover q cut j hj
      apply C.anchorEdge_has_unmarked_endpoint M anchor pos (c.getVert a)
      · simpa only [he] using hainc
      · rw [hcycleAnchor a]
        change c.cutSplitCycleAnchor cover q cut a = C.edge pos
        exact haedge.trans he.symm
    · obtain ⟨z, hzD, hzends⟩ := (cover D).meets_component f
      have hzout : z ∉ c.support := c.componentVertices_subset_compl D hzD
      apply C.degreeTwo_has_unmarked_endpoint M anchor hanchorInc pos z
      · rw [he]
        exact hzends
      · exact hdegree z hzout
    · have hadjacent := M.expandTransitions_edges_adjacent transition p i
      (hp.2 (Sum.inr i))
      have hpass := tour.toCyclicCircuit_exists_pass_of_edgesAdjacent M htour
        (transition i).left (transition i).right hadjacent
      apply C.transitionRight_has_unmarked_endpoint M anchor (transition i)
      · rw [c.forwardLastCutCycleTransition_center,
        hcycleAnchor i.1.1]
        exact c.forwardLastCutCycleTransition_left_eq_anchor hc cover hlast i
      · exact hpass
      · rw [c.forwardLastCutCycleTransition_right]
        exact he
  have hcopyLast : ∀ i : UncutActiveCycleCopy q cut,
    i.1.1 ≠ cycleLastIndex c.length := by
    intro i
    simpa only [cut, lastActiveCycleCopy] using i.2
  have hnext : C.anchorMarked M anchor
    (EdgeIndexedMultigraph.cyclicNext C.size C.size_pos start) = false := by
    have hrootInc : M.Inc x (C.edge start) := by
      rw [EdgeIndexedMultigraph.Inc, C.ends_edge, Sym2.mem_iff]
      exact Or.inl hstartVertex.symm
    rcases c.cutRootEdge_other_endpoint hc cover q cut anchor hcycleAnchor
      hcopyLast (C.edge start) hrootInc with h | h
    · obtain ⟨z, hzx, hzinc, hzanchor⟩ := h
      exact C.anchorEdge_next_unmarked M anchor start x z hstartVertex hzx
        hzinc hzanchor
    · obtain ⟨z, hzx, hzinc, hzdegree⟩ := h
      exact C.degreeTwo_next_unmarked M anchor hanchorInc start x z
        hstartVertex hzx hzinc hzdegree
  have hprev : C.anchorMarked M anchor
    (EdgeIndexedMultigraph.cyclicPrev C.size C.size_pos start) = false := by
    have hrootInc : M.Inc x (C.incoming M start) := by
      rw [EdgeIndexedMultigraph.Inc, C.ends_incoming, Sym2.mem_iff]
      exact Or.inr hstartVertex.symm
    rcases c.cutRootEdge_other_endpoint hc cover q cut anchor hcycleAnchor
      hcopyLast (C.incoming M start) hrootInc with h | h
    · obtain ⟨z, hzx, hzinc, hzanchor⟩ := h
      exact C.anchorEdge_prev_unmarked M anchor start x z hstartVertex hzx
        hzinc hzanchor
    · obtain ⟨z, hzx, hzinc, hzdegree⟩ := h
      exact C.degreeTwo_prev_unmarked M anchor hanchorInc start x z
        hstartVertex hzx hzinc hzdegree
  apply C.anchorMarked_toHasStrongSquareCycle M G x {z | z ∈ c.support}
    anchor hanchorInc
    hdegree (c.cutAugmentedTrailMultigraph_square_adj cover q cut)
    (c.cutAugmentedTrailMultigraph_cycle_edge cover q cut) start
    hstartVertex hstart hedge hnext hprev
  · change x ∈ c.support
    simpa only [c.getVert_zero] using c.getVert_mem_support 0
  · exact hcard

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[hasStrongSquareCycle_of_cutSplit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
Hamiltonian cycle in the square. -/
private lemma hasStrongSquareCycle_of_cutSplit [Fintype V] [DecidableEq V]
  (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length]
  (cut : ActiveCycleCopy (c.cycleEulerizationCompletion hc cover))
  (hlast : (c.cycleEulerizationCompletion hc cover).copies
    (cycleLastIndex c.length) = 0)
  (hcard : 3 ≤ Fintype.card V) : G.HasStrongSquareCycle x := by
  classical
  let q := c.cycleEulerizationCompletion hc cover
  let M := c.cutAugmentedTrailMultigraph cover q cut
  let transition := c.cutSplitCycleTransition hc cover q cut hlast
  have hinj : Function.Injective (M.transitionEdge transition) :=
    c.cutSplitCycleTransition_edge_injective hc cover q cut hlast
  obtain ⟨u, p, hp⟩ := c.exists_cutSplit_compressed_eulerian hc cover cut hlast
  let tour := M.expandTransitions transition p
  have htour : tour.IsEulerian :=
    M.expandTransitions_isEulerian transition hinj p hp
  have hzeroCut : (0 : Fin c.length) ≠ cut.1 := (cut.ne_zero q).symm
  let edge0 := c.cutOriginalEdge cover q cut 0 hzeroCut
  let _ : Nonempty (c.CutAugmentedTrailEdge cover q cut) := ⟨edge0⟩
  let C := tour.toCyclicCircuit M htour
  let cycleAnchor := c.cutSplitCycleAnchor cover q cut
  have hcycleInc : ∀ i : Fin c.length, M.Inc (c.getVert i) (cycleAnchor i) :=
    c.cutSplitCycleAnchor_inc cover q cut
  have hdegree : ∀ z ∉ c.support, M.degree z = 2 := by
    intro z hz
    exact c.cutAugmentedTrailMultigraph_degree_eq_two_of_not_mem
      hc cover q cut hz
  obtain ⟨anchor, hanchorInc, hcycleAnchor⟩ :=
    hc.exists_incident_anchor M cycleAnchor hcycleInc hdegree
  obtain ⟨start, ⟨hstartVertex, hstart⟩, _⟩ :=
    C.existsUnique_anchorMarked M anchor hanchorInc x
  have hedge (pos : Fin C.size) :
    C.anchorMarked M anchor pos = false ∨
      C.anchorMarked M anchor
        (EdgeIndexedMultigraph.cyclicNext C.size C.size_pos pos) = false := by
    rcases c.cutAugmentedTrailEdge_cases cover q cut (C.edge pos) with
      ⟨j, hj, he⟩ | ⟨D, f, he⟩ | ⟨i, he⟩
    · obtain ⟨a, _, hainc, haedge⟩ :=
      c.exists_cutSplitCycleAnchor_eq_original cover q cut j hj
      apply C.anchorEdge_has_unmarked_endpoint M anchor pos (c.getVert a)
      · simpa only [he] using hainc
      · rw [hcycleAnchor a]
        change c.cutSplitCycleAnchor cover q cut a = C.edge pos
        exact haedge.trans he.symm
    · obtain ⟨z, hzD, hzends⟩ := (cover D).meets_component f
      have hzout : z ∉ c.support := c.componentVertices_subset_compl D hzD
      apply C.degreeTwo_has_unmarked_endpoint M anchor hanchorInc pos z
      · rw [he]
        exact hzends
      · exact hdegree z hzout
    · have hadjacent := M.expandTransitions_edges_adjacent transition p i
      (hp.2 (Sum.inr i))
      have hpass := tour.toCyclicCircuit_exists_pass_of_edgesAdjacent M htour
        (transition i).left (transition i).right hadjacent
      obtain ⟨a, hcenter, hleft⟩ :=
        c.exists_cutSplitCycleTransition_center_anchor hc cover cut hlast i
      apply C.transitionRight_has_unmarked_endpoint M anchor (transition i)
      · rw [hcenter, hcycleAnchor a]
        exact hleft
      · exact hpass
      · rw [c.cutSplitCycleTransition_right]
        exact he
  have hcopyLast : ∀ i : UncutActiveCycleCopy q cut,
    i.1.1 ≠ cycleLastIndex c.length := by
    intro i
    exact i.1.ne_of_copies_eq_zero q _ hlast
  have hnext : C.anchorMarked M anchor
    (EdgeIndexedMultigraph.cyclicNext C.size C.size_pos start) = false := by
    have hrootInc : M.Inc x (C.edge start) := by
      rw [EdgeIndexedMultigraph.Inc, C.ends_edge, Sym2.mem_iff]
      exact Or.inl hstartVertex.symm
    rcases c.cutRootEdge_other_endpoint hc cover q cut anchor hcycleAnchor
      hcopyLast (C.edge start) hrootInc with h | h
    · obtain ⟨z, hzx, hzinc, hzanchor⟩ := h
      exact C.anchorEdge_next_unmarked M anchor start x z hstartVertex hzx
        hzinc hzanchor
    · obtain ⟨z, hzx, hzinc, hzdegree⟩ := h
      exact C.degreeTwo_next_unmarked M anchor hanchorInc start x z
        hstartVertex hzx hzinc hzdegree
  have hprev : C.anchorMarked M anchor
    (EdgeIndexedMultigraph.cyclicPrev C.size C.size_pos start) = false := by
    have hrootInc : M.Inc x (C.incoming M start) := by
      rw [EdgeIndexedMultigraph.Inc, C.ends_incoming, Sym2.mem_iff]
      exact Or.inr hstartVertex.symm
    rcases c.cutRootEdge_other_endpoint hc cover q cut anchor hcycleAnchor
      hcopyLast (C.incoming M start) hrootInc with h | h
    · obtain ⟨z, hzx, hzinc, hzanchor⟩ := h
      exact C.anchorEdge_prev_unmarked M anchor start x z hstartVertex hzx
        hzinc hzanchor
    · obtain ⟨z, hzx, hzinc, hzdegree⟩ := h
      exact C.degreeTwo_prev_unmarked M anchor hanchorInc start x z
        hstartVertex hzx hzinc hzdegree
  apply C.anchorMarked_toHasStrongSquareCycle M G x {z | z ∈ c.support}
    anchor hanchorInc
    hdegree (c.cutAugmentedTrailMultigraph_square_adj cover q cut)
    (c.cutAugmentedTrailMultigraph_cycle_edge cover q cut) start
    hstartVertex hstart hedge hnext hprev
  · change x ∈ c.support
    simpa only [c.getVert_zero] using c.getVert_mem_support 0
  · exact hcard

end SimpleGraph.Walk

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V} {x : V}
/--
[hasStrongSquareCycle_of_componentTrailCovers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
square. -/
private lemma hasStrongSquareCycle_of_componentTrailCovers
  [Fintype V] [DecidableEq V]
  (c : G.Walk x x) (hc : c.IsCycle)
  (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
  [NeZero c.length] (k : Fin c.length) (hk0 : k ≠ 0)
  (hbound : c.IsBoundVertex (c.getVert k))
  (hcard : 3 ≤ Fintype.card V) : G.HasStrongSquareCycle x := by
  let q := c.cycleEulerizationCompletion hc cover
  have hlastCases : q.copies (cycleLastIndex c.length) = 0 ∨
    q.copies (cycleLastIndex c.length) = 1 := by
    have hlt := q.copies_lt_two (cycleLastIndex c.length)
    omega
  obtain hlast | hlast := hlastCases
  · have hkCases : q.copies k = 0 ∨ q.copies k = 1 := by
    have hlt := q.copies_lt_two k
    omega
    obtain hk | hk := hkCases
    · exact c.hasStrongSquareCycle_of_split hc cover k hk0 hbound hlast hk hcard
    · let cut : ActiveCycleCopy q := ⟨k, hk⟩
      exact c.hasStrongSquareCycle_of_cutSplit hc cover cut hlast hcard
  · exact c.hasStrongSquareCycle_of_forwardLastCut hc cover hlast hcard
/-! ## FleischnerStrong -/
namespace SimpleGraph
universe u

end SimpleGraph.Walk

namespace SimpleGraph

/--
[hasStrongSquareCycle_of_card_eq_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma IsVertexConnected.hasStrongSquareCycle_of_card_eq_three
  {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  (hG : G.IsVertexConnected 2)
  (hcard : Fintype.card V = 3) (x : V) : G.HasStrongSquareCycle x := by
  classical
  obtain ⟨c, hc⟩ := hG.exists_cycle_through x
  have hlength_le : c.length ≤ Fintype.card V := by
    have htail := List.Nodup.length_le_card hc.isPath_tail.support_nodup
    rw [c.tail.length_support, Walk.length_tail] at htail
    have hpos : 0 < c.length := Walk.not_nil_iff_lt_length.mp hc.not_nil
    omega
  have hlength : c.length = Fintype.card V := by
    have := hc.three_le_length
    omega
  let f : G →g G.square := {
    toFun v := v
    map_rel' h := ⟨G.ne_of_adj h, Or.inl h⟩ }
  let p : G.square.Walk x x := c.map f
  have hhc : c.IsHamiltonianCycle :=
    Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr ⟨hc, hlength⟩
  have hp : p.IsHamiltonianCycle := by
    apply hhc.map
    exact Function.bijective_id
  refine ⟨p, hp, ?_, ?_⟩
  · have hsnd : p.snd = c.snd := by
    simp only [p, Walk.snd, Walk.getVert_map]
    rfl
    rw [hsnd]
    exact c.adj_snd hc.not_nil
  · have hpenultimate : p.penultimate = c.penultimate := by
    simp only [p, Walk.penultimate, Walk.length_map, Walk.getVert_map]
    rfl
    rw [hpenultimate]
    exact c.adj_penultimate hc.not_nil

end SimpleGraph

namespace SimpleGraph

/--
[IsVertexConnected.hasStrongSquareCycle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
lemma IsVertexConnected.hasStrongSquareCycle
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (hG : G.IsVertexConnected 2) :
-- imply
  G.HasStrongSquareCycle x :=
-- proof
  hG.hasStrongSquareCycle_card (Fintype.card V) rfl x

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-26
