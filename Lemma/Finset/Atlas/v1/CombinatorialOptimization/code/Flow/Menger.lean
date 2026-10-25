import Mathlib
import sympy.Basic
import Def.v1.Atlas.CombinatorialOptimization.code.Flow.Menger.Part2
open Finset BigOperators Classical NetworkFlow


namespace NetworkFlow

/--
[list_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/Menger.lean)
-/
@[path]
lemma list_crossing
  [Fintype V]
  [DecidableEq V]
  [DecidablePred P]
-- given
  (P : α → Prop) :
-- imply
  ∀ (l : List α) (hl : l ≠ []), P (l.head hl) → ¬ P (l.getLast hl) → ∃ e ∈ l.zip l.tail, P e.1 ∧ ¬ P e.2 := by
-- proof
  intro l hl hP_head hP_last
  induction l with
  | nil => exact absurd rfl hl
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [List.head_cons] at hP_head
      simp only [List.getLast_singleton] at hP_last
      exact absurd hP_head hP_last
    | cons b rest' =>
      simp only [List.head_cons] at hP_head
      by_cases hb : P b
      · have hne : (b :: rest') ≠ [] := List.cons_ne_nil b rest'
        have h_head : P ((b :: rest').head hne) := by simp [hb]
        have h_last : ¬ P ((b :: rest').getLast hne) := by
          have : (a :: b :: rest').getLast hl = (b :: rest').getLast hne := by
            simp [List.getLast_cons]
          rwa [← this]
        obtain ⟨e, he_mem, he_prop⟩ := ih hne h_head h_last
        exact ⟨e, List.mem_cons.mpr (Or.inr he_mem), he_prop⟩
      · exact ⟨(a, b), List.mem_cons.mpr (Or.inl rfl), hP_head, hb⟩

end NetworkFlow

namespace NetworkFlow

/--
[path_crosses_cut](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/Menger.lean)
-/
@[path]
lemma path_crosses_cut
  [Fintype V]
  [DecidableEq V]
  {G : DirectedGraph V}
  {p : DirPath G}
  {S : Finset V}
-- given
  (hs : G.s ∈ S)
  (ht : G.t ∉ S) :
-- imply
  ∃ e ∈ p.edges, e.1 ∈ S ∧ e.2 ∈ Sᶜ ∧ G.edge e.1 e.2 := by
-- proof
  have h_head : p.vertices.head p.nonempty ∈ S := by rw [p.starts_at_s]; exact hs
  have h_last : p.vertices.getLast p.nonempty ∉ S := by rw [p.ends_at_t]; exact ht
  obtain ⟨e, he_mem, he_in, he_out⟩ :=
    list_crossing (· ∈ S) p.vertices p.nonempty h_head h_last
  exact ⟨e, he_mem, he_in, Finset.mem_compl.mpr he_out, p.edges_valid e he_mem⟩

end NetworkFlow

namespace NetworkFlow

/--
[edgeDisjointPaths_le_cutSize](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/Menger.lean)
-/
@[path]
lemma edgeDisjointPaths_le_cutSize
  [Fintype V]
  [DecidableEq V]
  {G : DirectedGraph V}
  {k : ℕ}
  {edp : EdgeDisjointPaths G k}
  {S : Finset V}
-- given
  (hs : G.s ∈ S)
  (ht : G.t ∉ S) :
-- imply
  k ≤ (Finset.univ.filter (fun p : V × V => p.1 ∈ S ∧ p.2 ∈ Sᶜ ∧ G.edge p.1 p.2)).card := by
-- proof
  have h_cross : ∀ i : Fin k, ∃ e, e ∈ (edp.paths i).edges ∧
    e ∈ Finset.univ.filter (fun p : V × V => p.1 ∈ S ∧ p.2 ∈ Sᶜ ∧ G.edge p.1 p.2) := by
    intro i
    obtain ⟨e, he_mem, he_S, he_Sc, he_edge⟩ := path_crosses_cut G (edp.paths i) S hs ht
    exact ⟨e, he_mem, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he_S, he_Sc, he_edge⟩⟩
  choose crossing h_crossing_mem h_crossing_in_cut using h_cross
  have h_inj : Function.Injective crossing := by
    intro i j hij
    by_contra h_ne
    exact edp.disjoint i j h_ne (crossing i) ⟨h_crossing_mem i, hij ▸ h_crossing_mem j⟩
  calc k = Fintype.card (Fin k) := (Fintype.card_fin k).symm
    _ = (Finset.univ : Finset (Fin k)).card := Finset.card_univ.symm
    _ = (Finset.univ.image crossing).card :=
      (Finset.card_image_of_injective _ h_inj).symm
    _ ≤ (Finset.univ.filter (fun p : V × V =>
      p.1 ∈ S ∧ p.2 ∈ Sᶜ ∧ G.edge p.1 p.2)).card :=
      Finset.card_le_card (fun e he => by
        rw [Finset.mem_image] at he
        obtain ⟨i, _, rfl⟩ := he
        exact h_crossing_in_cut i)

end NetworkFlow

namespace NetworkFlow

/--
[maxEdgeDisjointPaths_le_minSTCutSize](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/Menger.lean)
-/
@[path]
lemma maxEdgeDisjointPaths_le_minSTCutSize
  [Fintype V]
  [DecidableEq V]
  {G : DirectedGraph V} :
-- imply
  maxEdgeDisjointPaths G ≤ minSTCutSize G := by
-- proof
  unfold maxEdgeDisjointPaths minSTCutSize
  apply Finset.sup'_le
  intro ⟨k, hk⟩ hmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  apply Finset.le_inf'
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  obtain ⟨hsS, htS⟩ := hS
  obtain ⟨edp⟩ := hmem
  exact edgeDisjointPaths_le_cutSize G k edp S hsS htS

end NetworkFlow

namespace NetworkFlow

/--
[exists_maxFlow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/Menger.lean)
-/
@[path]
lemma exists_maxFlow
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V} :
-- imply
  ∃ fl : STFlow N, NoAugmentingPath N fl := by
-- proof
  set S : Set (V → V → ℝ) := { f | (∀ u v, 0 ≤ f u v) ∧ (∀ u v, f u v ≤ N.cap u v) ∧
    (∀ v, v ≠ N.s → v ≠ N.t → ∑ u : V, f u v = ∑ u : V, f v u) }
  have hS_ne : S.Nonempty :=
    ⟨fun _ _ => 0, fun _ _ => le_refl _, fun u v => N.cap_nonneg u v, fun _ _ _ => by simp⟩
  have hS_closed : IsClosed S := by
    have h1 : IsClosed { f : V → V → ℝ | ∀ u v, 0 ≤ f u v } := by
      have : { f : V → V → ℝ | ∀ u v, 0 ≤ f u v } = ⋂ u, ⋂ v, { f | 0 ≤ f u v } := by
        ext f; simp [Set.mem_iInter]
      rw [this]
      exact isClosed_iInter (fun u => isClosed_iInter (fun v =>
        isClosed_le continuous_const ((continuous_apply v).comp (continuous_apply u))))
    have h2 : IsClosed { f : V → V → ℝ | ∀ u v, f u v ≤ N.cap u v } := by
      have : { f : V → V → ℝ | ∀ u v, f u v ≤ N.cap u v } = ⋂ u, ⋂ v, { f | f u v ≤ N.cap u v } := by
        ext f; simp [Set.mem_iInter]
      rw [this]
      exact isClosed_iInter (fun u => isClosed_iInter (fun v =>
        isClosed_le ((continuous_apply v).comp (continuous_apply u)) continuous_const))
    have h3 : IsClosed { f : V → V → ℝ | ∀ v, v ≠ N.s → v ≠ N.t →
      ∑ u : V, f u v = ∑ u : V, f v u } := by
      have : { f : V → V → ℝ | ∀ v, v ≠ N.s → v ≠ N.t → ∑ u : V, f u v = ∑ u : V, f v u } =
        ⋂ (v : V), ⋂ (_ : v ≠ N.s), ⋂ (_ : v ≠ N.t),
          { f | ∑ u : V, f u v = ∑ u : V, f v u } := by
        ext f; simp [Set.mem_iInter]
      rw [this]
      exact isClosed_iInter (fun v => isClosed_iInter (fun _ => isClosed_iInter (fun _ =>
        isClosed_eq
          (continuous_finset_sum _ (fun u _ => (continuous_apply v).comp (continuous_apply u)))
          (continuous_finset_sum _ (fun u _ => (continuous_apply u).comp (continuous_apply v))))))
    have hS_eq : S = { f | ∀ u v, 0 ≤ f u v } ∩ { f | ∀ u v, f u v ≤ N.cap u v } ∩
      { f | ∀ v, v ≠ N.s → v ≠ N.t → ∑ u : V, f u v = ∑ u : V, f v u } := by
      ext f; simp only [S, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
    rw [hS_eq]; exact (h1.inter h2).inter h3
  have hS_bounded : Bornology.IsBounded S := by
    apply (isCompact_univ_pi (fun u => isCompact_univ_pi
      (fun v => isCompact_Icc (a := 0) (b := N.cap u v)))).isBounded.subset
    intro f hf; simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro u v; exact ⟨hf.1 u v, hf.2.1 u v⟩
  have hS_compact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
  have hfv_cont : ContinuousOn (fun f : V → V → ℝ => ∑ v : V, f N.s v - ∑ v : V, f v N.s) S :=
    (Continuous.sub
      (continuous_finset_sum _ (fun v _ => (continuous_apply v).comp (continuous_apply N.s)))
      (continuous_finset_sum _ (fun v _ => (continuous_apply N.s).comp (continuous_apply v)))).continuousOn
  obtain ⟨fmax, hfmax_mem, _, hfmax_ge⟩ := hS_compact.exists_sSup_image_eq_and_ge hS_ne hfv_cont
  set fl : STFlow N := ⟨fmax, hfmax_mem.1, hfmax_mem.2.1, hfmax_mem.2.2⟩
  have hIsMax : IsMaxFlow N fl := by
    intro fl'
    exact hfmax_ge fl'.f ⟨fl'.flow_nonneg, fl'.flow_cap, fl'.conservation⟩
  exact ⟨fl, (isMaxFlow_iff_noAugmentingPath N fl).mp hIsMax⟩

end NetworkFlow

namespace NetworkFlow

/--
[cutCapacity_eq_crossing_edges](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/Menger.lean)
-/
@[path]
lemma cutCapacity_eq_crossing_edges
  [Fintype V]
  [DecidableEq V]
  {G : DirectedGraph V}
  {C : STCut G.toFlowNetwork} :
-- imply
  cutCapacity G.toFlowNetwork C = ↑(Finset.univ.filter (fun p : V × V => p.1 ∈ C.S ∧ p.2 ∈ C.Sᶜ ∧ G.edge p.1 p.2)).card := by
-- proof
  unfold cutCapacity DirectedGraph.toFlowNetwork
  simp only
  rw [show (Finset.univ.filter (fun p : V × V => p.1 ∈ C.S ∧ p.2 ∈ C.Sᶜ ∧ G.edge p.1 p.2)) =
    (C.S ×ˢ C.Sᶜ).filter (fun p => G.edge p.1 p.2) from by
      ext ⟨u, v⟩; simp [Finset.mem_filter, Finset.mem_product, and_assoc]]
  rw [Finset.card_filter]
  push_cast
  rw [← Finset.sum_product']

end NetworkFlow


-- created on 2026-10-23
