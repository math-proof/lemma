import Mathlib
import sympy.Basic
import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
open SimpleGraph
open EdgeIndexedMultigraph
open IndexedWalk


namespace SimpleGraph.EdgeIndexedMultigraph


namespace SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

/--
[isTrail_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma isTrail_iff
  {M : EdgeIndexedMultigraph V E}
  {u v : V}
  {p : M.IndexedWalk u v} :
-- imply
  p.IsTrail ↔ p.edges.Nodup :=
-- proof
  Iff.rfl

end SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

namespace SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

/--
[isEulerian_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma isEulerian_iff
  {M : EdgeIndexedMultigraph V E}
  {u v : V}
  {p : M.IndexedWalk u v} :
-- imply
  p.IsEulerian ↔ p.IsTrail ∧ ∀ e, e ∈ p.edges :=
-- proof
  Iff.rfl

end SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

namespace SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

/--
[support_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma support_nil
  {M : EdgeIndexedMultigraph V E}
  {v : V} :
-- imply
  (IndexedWalk.nil v : M.IndexedWalk v v).support = [v] :=
-- proof
  rfl

end SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

namespace SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

/--
[support_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma support_cons
  {M : EdgeIndexedMultigraph V E}
  {u v w : V}
  {e : E}
  {p : M.IndexedWalk v w}
-- given
  (he : M.ends e = s(u, v)) :
-- imply
  (IndexedWalk.cons e he p).support = u :: p.support :=
-- proof
  rfl

end SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

namespace SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

/--
[edges_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma edges_nil
  {M : EdgeIndexedMultigraph V E}
  {v : V} :
-- imply
  (IndexedWalk.nil v : M.IndexedWalk v v).edges = [] :=
-- proof
  rfl

end SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[inc_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma inc_iff
  {M : EdgeIndexedMultigraph V E}
  {v : V}
  {e : E} :
-- imply
  M.Inc v e ↔ v ∈ M.ends e :=
-- proof
  Iff.rfl

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[underlying_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma underlying_adj
  {M : EdgeIndexedMultigraph V E}
  {u v : V} :
-- imply
  M.underlying.Adj u v ↔ ∃ e, M.ends e = s(u, v) := by
-- proof
  rw [underlying, fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨e, he⟩, _⟩
    exact ⟨e, he⟩
  · rintro ⟨e, he⟩
    refine ⟨⟨e, he⟩, ?_⟩
    intro huv
    subst v
    exact M.loopless e u he

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

/--
[support_toWalk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma support_toWalk
  {u v : V}
  {p : M.IndexedWalk u v} :
-- imply
  p.toWalk.support = p.support := by
-- proof
  induction p with
  | nil => rfl
  | cons e he p ih => exact congrArg (fun l ↦ _ :: l) ih

end SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

namespace SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

/--
[edges_toWalk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma edges_toWalk
  {M : EdgeIndexedMultigraph V E}
  {u v : V}
  {p : M.IndexedWalk u v} :
-- imply
  p.toWalk.edges = p.edges.map M.ends := by
-- proof
  induction p with
  | nil => rfl
  | @cons u v w e he p ih =>
    change s(u, v) :: p.toWalk.edges = M.ends e :: List.map M.ends p.edges
    rw [he, ih]

end SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

namespace SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

/--
[length_toWalk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma length_toWalk
  {M : EdgeIndexedMultigraph V E}
  {u v : V}
  {p : M.IndexedWalk u v} :
-- imply
  p.toWalk.length = p.edges.length := by
-- proof
  calc
    p.toWalk.length = p.toWalk.edges.length := p.toWalk.length_edges.symm
    _ = p.edges.length := by rw [edges_toWalk, List.length_map]

end SimpleGraph.EdgeIndexedMultigraph.IndexedWalk

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[degree_eq_ncard_inc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma degree_eq_ncard_inc
  {M : EdgeIndexedMultigraph V E}
  {v : V} :
-- imply
  M.degree v = {e | M.Inc v e}.ncard :=
-- proof
  rfl

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[disjointSum_ends_inl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma disjointSum_ends_inl
  {M : EdgeIndexedMultigraph V E}
  {N : EdgeIndexedMultigraph V F}
  {e : E} :
-- imply
  (M.disjointSum N).ends (Sum.inl e) = M.ends e :=
-- proof
  rfl

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[disjointSum_ends_inr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma disjointSum_ends_inr
  {M : EdgeIndexedMultigraph V E}
  {N : EdgeIndexedMultigraph V F}
  {f : F} :
-- imply
  (M.disjointSum N).ends (Sum.inr f) = N.ends f :=
-- proof
  rfl

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[disjointSum_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma disjointSum_degree
  [Finite E] [Finite F]
  {M : EdgeIndexedMultigraph V E}
  {N : EdgeIndexedMultigraph V F}
  {v : V} :
-- imply
  (M.disjointSum N).degree v = M.degree v + N.degree v := by
-- proof
  calc
    (M.disjointSum N).degree v =
      Nat.card {e : E ⊕ F // (M.disjointSum N).Inc v e} := by
      rw [degree]
      exact (Nat.card_coe_set_eq
        {e : E ⊕ F | (M.disjointSum N).Inc v e}).symm
    _ = Nat.card ({e : E // M.Inc v e} ⊕ {f : F // N.Inc v f}) :=
      Nat.card_congr (M.disjointSumIncidenceEquiv N v)
    _ = Nat.card {e : E // M.Inc v e} + Nat.card {f : F // N.Inc v f} :=
      Nat.card_sum
    _ = M.degree v + N.degree v := by
      rw [degree, degree]
      exact congrArg₂ (· + ·)
        (Nat.card_coe_set_eq {e : E | M.Inc v e})
        (Nat.card_coe_set_eq {f : F | N.Inc v f})

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[disjointSum_connected_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma disjointSum_connected_left
  {M : EdgeIndexedMultigraph V E}
  {N : EdgeIndexedMultigraph V F}
-- given
  (hM : M.underlying.Connected) :
-- imply
  (M.disjointSum N).underlying.Connected := by
-- proof
  let f : M.underlying →g (M.disjointSum N).underlying := {
    toFun := id
    map_rel' := by
      intro u v huv
      obtain ⟨e, he⟩ := M.underlying_adj.mp huv
      apply (M.disjointSum N).underlying_adj.mpr
      exact ⟨Sum.inl e, he⟩ }
  apply hM.map f
  intro v
  exact ⟨v, rfl⟩

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[even_sum_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma even_sum_degree
  [Fintype V] [Finite E]
  {M : EdgeIndexedMultigraph V E} :
-- imply
  Even (∑ v, M.degree v) := by
-- proof
  classical
  let _ := Fintype.ofFinite E
  have htotal : Even (∑ z : V ⊕ E, M.incidenceGraph.degree z) := by
    rw [M.incidenceGraph.sum_degrees_eq_twice_card_edges]
    exact ⟨M.incidenceGraph.edgeFinset.card, by omega⟩
  rw [Fintype.sum_sum_type] at htotal
  simp_rw [M.incidenceGraph_degree_inl, M.incidenceGraph_degree_inr] at htotal
  have hedge : Even (∑ _e : E, 2) := by
    exact ⟨Fintype.card E, by simp; omega⟩
  exact (Nat.even_add.mp htotal).mpr hedge

end SimpleGraph.EdgeIndexedMultigraph

/--
[incidenceGraph_adj_inl_inr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma incidenceGraph_adj_inl_inr (v : V) (e : E) :
  M.incidenceGraph.Adj (Sum.inl v) (Sum.inr e) ↔ M.Inc v e :=
  Iff.rfl

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[incidenceGraph_adj_inr_inl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma incidenceGraph_adj_inr_inl (e : E) (v : V) :
  M.incidenceGraph.Adj (Sum.inr e) (Sum.inl v) ↔ M.Inc v e :=
  Iff.rfl

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[not_incidenceGraph_adj_inl_inl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma not_incidenceGraph_adj_inl_inl (u v : V) :
  ¬M.incidenceGraph.Adj (Sum.inl u) (Sum.inl v) := by
  intro h
  exact h

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[not_incidenceGraph_adj_inr_inr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma not_incidenceGraph_adj_inr_inr (e f : E) :
  ¬M.incidenceGraph.Adj (Sum.inr e) (Sum.inr f) := by
  intro h
  exact h

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[exists_ends](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma exists_ends (e : E) :
  ∃ u v, u ≠ v ∧ M.ends e = s(u, v) := by
  induction h : M.ends e using Sym2.inductionOn with
  | _ u v =>
    refine ⟨u, v, ?_, rfl⟩
    intro huv
    subst v
    exact M.loopless e u h

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[exists_underlying_adj_of_inc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma exists_underlying_adj_of_inc {v : V} {e : E} (h : M.Inc v e) :
  ∃ w, M.underlying.Adj v w := by
  obtain ⟨u, w, huw, he⟩ := M.exists_ends e
  rw [Inc, he] at h
  obtain hvu | hvw := Sym2.mem_iff.mp h
  · subst v
    exact ⟨w, M.underlying_adj.mpr ⟨e, he⟩⟩
  · subst v
    exact ⟨u, M.underlying_adj.mpr ⟨e, he.trans Sym2.eq_swap⟩⟩

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[reachable_inl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
incidence subdivision. -/
private lemma reachable_inl {u v : V} (h : M.underlying.Reachable u v) :
  M.incidenceGraph.Reachable (Sum.inl u) (Sum.inl v) := by
  rw [reachable_iff_reflTransGen] at h ⊢
  apply h.lift' Sum.inl
  intro a b hab
  change Relation.ReflTransGen M.incidenceGraph.Adj (Sum.inl a) (Sum.inl b)
  obtain ⟨e, he⟩ := M.underlying_adj.mp hab
  have hae : M.incidenceGraph.Adj (Sum.inl a) (Sum.inr e) := by
    change M.Inc a e
    simp [Inc, he]
  have heb : M.incidenceGraph.Adj (Sum.inr e) (Sum.inl b) := by
    change M.Inc b e
    simp [Inc, he]
  exact (Relation.ReflTransGen.single hae).trans (Relation.ReflTransGen.single heb)

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[incidence_support_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma incidence_support_anchor
  (z : M.incidenceGraph.support) :
  ∃ v : M.underlying.support,
    M.incidenceGraph.Reachable z.1 (Sum.inl v.1) := by
  obtain ⟨z, hz⟩ := z
  cases z with
  | inl v =>
    rw [M.incidenceGraph.mem_support] at hz
    obtain ⟨z, hvz⟩ := hz
    cases z with
    | inl w => exact False.elim (M.not_incidenceGraph_adj_inl_inl v w hvz)
    | inr e =>
      obtain ⟨w, hvw⟩ := M.exists_underlying_adj_of_inc hvz
      exact ⟨⟨v, M.underlying.mem_support.mpr ⟨w, hvw⟩⟩, ⟨Walk.nil⟩⟩
  | inr e =>
    obtain ⟨u, v, huv, he⟩ := M.exists_ends e
    have huv' : M.underlying.Adj u v := M.underlying_adj.mpr ⟨e, he⟩
    let u' : M.underlying.support :=
      ⟨u, M.underlying.mem_support.mpr ⟨v, huv'⟩⟩
    have heu : M.incidenceGraph.Adj (Sum.inr e) (Sum.inl u) := by
      change M.Inc u e
      simp [Inc, he]
    exact ⟨u', ⟨Walk.cons heu Walk.nil⟩⟩

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[incidenceGraph_connectedSupport](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
true in its incidence subdivision. -/
private lemma incidenceGraph_connectedSupport
  (hconn : (M.underlying.induce M.underlying.support).Connected) :
  (M.incidenceGraph.induce M.incidenceGraph.support).Connected := by
  refine { preconnected := ?_, nonempty := ?_ }
  · intro z w
    obtain ⟨u, hzu⟩ := M.incidence_support_anchor z
    obtain ⟨v, hwv⟩ := M.incidence_support_anchor w
    have huv : M.underlying.Reachable u.1 v.1 :=
      (hconn u v).map (Embedding.induce M.underlying.support).toHom
    have hzw : M.incidenceGraph.Reachable z.1 w.1 :=
      hzu.trans (M.reachable_inl huv) |>.trans hwv.symm
    exact hzw.induce_support z.2 w.2
  · obtain ⟨u⟩ := hconn.nonempty
    have hu := u.2
    rw [M.underlying.mem_support] at hu
    obtain ⟨v, huv⟩ := hu
    obtain ⟨e, he⟩ := M.underlying_adj.mp huv
    refine ⟨⟨Sum.inl u.1, M.incidenceGraph.mem_support.mpr ?_⟩⟩
    exact ⟨Sum.inr e, by simp [Inc, he]⟩

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[incidenceGraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
subdivision. -/
private lemma incidenceGraph_connected (hM : M.underlying.Connected) :
  M.incidenceGraph.Connected := by
  obtain ⟨r⟩ := hM.nonempty
  have reach : ∀ z : V ⊕ E, M.incidenceGraph.Reachable (Sum.inl r) z := by
    intro z
    cases z with
    | inl v => exact M.reachable_inl (hM r v)
    | inr e =>
      obtain ⟨u, v, huv, he⟩ := M.exists_ends e
      apply (M.reachable_inl (hM r u)).trans
      exact ⟨Walk.cons (by simp [Inc, he]) Walk.nil⟩
  refine { preconnected := ?_, nonempty := ⟨Sum.inl r⟩ }
  intro a b
  exact (reach a).symm.trans (reach b)

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[incidenceGraph_degree_inl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma incidenceGraph_degree_inl [Fintype V] [Fintype E] [DecidableEq V] (v : V) :
  M.incidenceGraph.degree (Sum.inl v) = M.degree v := by
  classical
  have hset : M.incidenceGraph.neighborSet (Sum.inl v) =
    Sum.inr '' {e | M.Inc v e} := by
    ext z
    cases z <;> simp [mem_neighborSet]
  rw [← ncard_neighborSet, hset, Set.ncard_image_of_injective _ Sum.inr_injective]
  rfl

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[incidenceGraph_degree_inr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma incidenceGraph_degree_inr [Fintype V] [Fintype E] [DecidableEq V] (e : E) :
  M.incidenceGraph.degree (Sum.inr e) = 2 := by
  classical
  have hset : M.incidenceGraph.neighborSet (Sum.inr e) =
    Sum.inl '' {v | M.Inc v e} := by
    ext z
    cases z <;> simp [mem_neighborSet]
  obtain ⟨u, v, huv, he⟩ := M.exists_ends e
  have hends : {w | M.Inc w e} = ({u, v} : Set V) := by
    ext w
    simp [Inc, he, Sym2.mem_iff]
  rw [← ncard_neighborSet, hset, Set.ncard_image_of_injective _ Sum.inl_injective,
    hends, Set.ncard_pair huv]

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[edgeProjection_count](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma edgeProjection_count [DecidableEq V] [DecidableEq E]
  (l : List (V ⊕ E)) (e : E) :
  (edgeProjection l).count e = l.countP (· = Sum.inr e) := by
  induction l with
  | nil => rfl
  | cons z l ih =>
    cases z with
    | inl v =>
      simpa [edgeProjection] using ih
    | inr f =>
      by_cases hfe : f = e
      · subst f
        simp [edgeProjection, List.count_cons_self, ih]
      · simp [edgeProjection, List.count_cons_of_ne hfe, hfe, ih]

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[walk_countP_edges_add_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma walk_countP_edges_add_endpoints {W : Type*} [DecidableEq W]
  {H : SimpleGraph W} {u v : W} (p : H.Walk u v) (z : W) :
  p.edges.countP (z ∈ ·) + (if z = u then 1 else 0) + (if z = v then 1 else 0) =
    2 * p.support.countP (· = z) := by
  induction p with
  | @nil t =>
    by_cases hzt : z = t
    · subst z
      simp
    · simp [hzt, Ne.symm hzt]
  | @cons u w v h p ih =>
    simp only [SimpleGraph.Walk.edges_cons, List.countP_cons,
      SimpleGraph.Walk.support_cons]
    have huw : u ≠ w := H.ne_of_adj h
    by_cases hzu : z = u
    · subst z
      simp [huw, Sym2.mem_iff] at ih ⊢
      omega
    · by_cases hzw : z = w
      · subst z
        simp [hzu, Ne.symm hzu, Sym2.mem_iff] at ih ⊢
        omega
      · simp [hzu, Ne.symm hzu, hzw, Sym2.mem_iff] at ih ⊢
        omega

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[walk_two_mul_count_tail_support](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma walk_two_mul_count_tail_support {W : Type*} [DecidableEq W]
  {H : SimpleGraph W} {u : W} (p : H.Walk u u) (z : W) :
  2 * p.support.tail.countP (· = z) = p.edges.countP (z ∈ ·) := by
  have h := walk_countP_edges_add_endpoints p z
  have hsupp : p.support.countP (· = z) =
    (if z = u then 1 else 0) + p.support.tail.countP (· = z) := by
    calc
      p.support.countP (· = z) =
        (u :: p.support.tail).countP (· = z) := by
        exact congrArg (List.countP (· = z)) p.cons_tail_support.symm
      _ = (if z = u then 1 else 0) + p.support.tail.countP (· = z) := by
        by_cases hzu : z = u
        · subst z
          simp only [List.countP_cons, decide_eq_true_eq]
          omega
        · simp only [List.countP_cons, decide_eq_true_eq, hzu, Ne.symm hzu]
          exact Nat.add_comm _ _
  rw [hsupp] at h
  by_cases hzu : z = u
  · simp [hzu] at h ⊢
    omega
  · simp [hzu] at h ⊢
    omega

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[indexedWalkOfIncidence_edges](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma indexedWalkOfIncidence_edges [DecidableEq V] {u v : V}
  (p : M.incidenceGraph.Walk (Sum.inl u) (Sum.inl v)) (hp : p.IsTrail) :
  (M.indexedWalkOfIncidence p hp).edges = edgeProjection p.support :=
  (M.collapseIncidence p hp).edges_eq

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[exists_eulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
incidence subdivision. The indexed-edge vertices distinguish parallel edges. -/
private lemma exists_eulerian [Finite V] [Finite E] [DecidableEq V] [DecidableEq E]
  (hconn : M.underlying.Connected) (heven : ∀ v, Even (M.degree v)) :
  ∃ (z : V ⊕ E) (p : M.incidenceGraph.Walk z z), p.IsEulerian := by
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  apply (M.incidenceGraph_connected hconn).exists_isEulerian
  intro z
  cases z with
  | inl v =>
    rw [M.incidenceGraph_degree_inl]
    exact heven v
  | inr e =>
    rwa [M.incidenceGraph_degree_inr]

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[exists_indexedEulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma exists_indexedEulerian
  [Finite V] [Finite E]
  {M : EdgeIndexedMultigraph V E}
-- given
  (hconn : M.underlying.Connected)
  (heven : ∀ v, Even (M.degree v)) :
-- imply
  ∃ (u : V) (p : M.IndexedWalk u u), p.IsEulerian := by
-- proof
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  by_cases hE : Nonempty E
  · obtain ⟨e⟩ := hE
    obtain ⟨z, p, hp⟩ := M.exists_eulerian hconn heven
    obtain ⟨u, v, huv, he⟩ := M.exists_ends e
    have hue : M.incidenceGraph.Adj (Sum.inl u) (Sum.inr e) := by
      simp [Inc, he]
    have hu_support : Sum.inl u ∈ p.support :=
      hp.mem_support_of_not_isIsolated hue.not_isIsolated_left
    let q := p.rotate (Sum.inl u) hu_support
    have hq_trail : q.IsTrail := hp.isTrail.rotate hu_support
    have hq_eulerian : q.IsEulerian := by
      apply hq_trail.isEulerian_of_forall_mem
      intro f hf
      apply (p.rotate_edges (Sum.inl u) hu_support).mem_iff.mpr
      exact hp.mem_edges_iff.mpr hf
    have htail_count (f : E) :
      q.support.tail.countP (· = Sum.inr f) = 1 := by
      have hcount := walk_two_mul_count_tail_support q (Sum.inr f)
      rw [hq_eulerian.countP_edges_eq_degree,
        M.incidenceGraph_degree_inr] at hcount
      omega
    have hprojection : edgeProjection q.support = edgeProjection q.support.tail := by
      calc
        edgeProjection q.support =
          edgeProjection (Sum.inl u :: q.support.tail) := by
          exact congrArg edgeProjection q.cons_tail_support.symm
        _ = edgeProjection q.support.tail := rfl
    let r := M.indexedWalkOfIncidence q hq_trail
    have hr_count (f : E) : r.edges.count f = 1 := by
      rw [M.indexedWalkOfIncidence_edges q hq_trail, hprojection,
        edgeProjection_count]
      exact htail_count f
    refine ⟨u, r, ?_⟩
    constructor
    · apply List.nodup_iff_count_le_one.mpr
      intro f
      rw [hr_count f]
    · intro f
      apply List.count_pos_iff.mp
      rw [hr_count f]
      omega
  · let _ : IsEmpty E := ⟨fun e ↦ hE ⟨e⟩⟩
    obtain ⟨u⟩ := hconn.nonempty
    refine ⟨u, .nil u, ?_⟩
    exact ⟨by simp [IndexedWalk.IsTrail], fun e ↦ isEmptyElim e⟩

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[exists_eulerian_connectedSupport](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
an Euler circuit in its incidence subdivision. -/
private lemma exists_eulerian_connectedSupport [Finite V] [Finite E]
  [DecidableEq V] [DecidableEq E]
  (hconn : (M.underlying.induce M.underlying.support).Connected)
  (heven : ∀ v, Even (M.degree v)) :
  ∃ (z : V ⊕ E) (p : M.incidenceGraph.Walk z z), p.IsEulerian := by
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  apply ConnectedSupport.exists_isEulerian (M.incidenceGraph_connectedSupport hconn)
  intro z
  cases z with
  | inl v =>
    rw [M.incidenceGraph_degree_inl]
    exact heven v
  | inr e =>
    rwa [M.incidenceGraph_degree_inr]

end SimpleGraph.EdgeIndexedMultigraph

namespace SimpleGraph.EdgeIndexedMultigraph

/--
[exists_indexedEulerian_connectedSupport](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma exists_indexedEulerian_connectedSupport
  [Finite V] [Finite E]
  {M : EdgeIndexedMultigraph V E}
-- given
  (hconn : (M.underlying.induce M.underlying.support).Connected)
  (heven : ∀ v, Even (M.degree v)) :
-- imply
  ∃ (u : V) (p : M.IndexedWalk u u), p.IsEulerian := by
-- proof
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  by_cases hE : Nonempty E
  · obtain ⟨e⟩ := hE
    obtain ⟨z, p, hp⟩ := M.exists_eulerian_connectedSupport hconn heven
    obtain ⟨u, v, huv, he⟩ := M.exists_ends e
    have hue : M.incidenceGraph.Adj (Sum.inl u) (Sum.inr e) := by
      simp [Inc, he]
    have hu_support : Sum.inl u ∈ p.support :=
      hp.mem_support_of_not_isIsolated hue.not_isIsolated_left
    let q := p.rotate (Sum.inl u) hu_support
    have hq_trail : q.IsTrail := hp.isTrail.rotate hu_support
    have hq_eulerian : q.IsEulerian := by
      apply hq_trail.isEulerian_of_forall_mem
      intro f hf
      apply (p.rotate_edges (Sum.inl u) hu_support).mem_iff.mpr
      exact hp.mem_edges_iff.mpr hf
    have htail_count (f : E) :
      q.support.tail.countP (· = Sum.inr f) = 1 := by
      have hcount := walk_two_mul_count_tail_support q (Sum.inr f)
      rw [hq_eulerian.countP_edges_eq_degree,
        M.incidenceGraph_degree_inr] at hcount
      omega
    have hprojection : edgeProjection q.support = edgeProjection q.support.tail := by
      calc
        edgeProjection q.support =
          edgeProjection (Sum.inl u :: q.support.tail) := by
          exact congrArg edgeProjection q.cons_tail_support.symm
        _ = edgeProjection q.support.tail := rfl
    let r := M.indexedWalkOfIncidence q hq_trail
    have hr_count (f : E) : r.edges.count f = 1 := by
      rw [M.indexedWalkOfIncidence_edges q hq_trail, hprojection,
        edgeProjection_count]
      exact htail_count f
    refine ⟨u, r, ?_⟩
    constructor
    · apply List.nodup_iff_count_le_one.mpr
      intro f
      rw [hr_count f]
    · intro f
      apply List.count_pos_iff.mp
      rw [hr_count f]
      omega
  · let _ : IsEmpty E := ⟨fun e ↦ hE ⟨e⟩⟩
    obtain ⟨u⟩ := hconn.nonempty
    have hu := M.underlying.mem_support.mp u.2
    obtain ⟨v, huv⟩ := hu
    obtain ⟨e, he⟩ := M.underlying_adj.mp huv
    exact isEmptyElim e

end SimpleGraph.EdgeIndexedMultigraph

/--
[edges_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma edges_cons_eq
  {M : EdgeIndexedMultigraph V E}
  {u v w : V}
  {e : E}
  {p : M.IndexedWalk v w}
-- given
  (he : M.ends e = s(u, v)) :
-- imply
  (IndexedWalk.cons e he p).edges = e :: p.edges := by
-- proof
  apply SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.edges_cons M e he p


-- created on 2026-10-20
-- updated on 2026-10-23
