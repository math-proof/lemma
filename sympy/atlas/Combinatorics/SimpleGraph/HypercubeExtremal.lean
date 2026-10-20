/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean -/

import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Set.Card

/-!
# Hypercube Turán extremal number for `Q_n`

Primary source: Marko Pejić, *On the Turán Density of C10 in the Hypercube*,
arXiv:2608.12237v2 (defining text, lines 122-123, with subgraph and `H`-free
conventions at lines 136-140).

Scope: this file defines the `n`-dimensional hypercube `Q_n` as a Mathlib
`SimpleGraph` on `Fin n → Bool` and defines `ex(Q_n, H)` as the maximum edge
count over `H`-free `SimpleGraph.Subgraph`s, including non-spanning ones.
It proves the adjacency characterization, the lower bound into the maximum,
the upper bound by the edges of `Q_n`, attainment under nonemptiness, and the
`Q_0` boundary value. It does not formalize the asymptotic density, existence
of its limit, or the paper's `C_6`/`C_10` bounds.
-/

namespace SimpleGraph

/-- The `n`-dimensional hypercube `Q_n`: vertices are `Fin n → Bool`, with an edge
between two vertices exactly when they differ in exactly one coordinate. -/
def hypercubeGraph (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel (fun x y => ∃! i, x i ≠ y i)

/-- Adjacency in `Q_n` holds exactly when the endpoints differ in a unique coordinate. -/
@[simp]
theorem hypercubeGraph_adj (n : ℕ) (x y : Fin n → Bool) :
    (hypercubeGraph n).Adj x y ↔ ∃! i, x i ≠ y i := by
  unfold hypercubeGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · obtain ⟨i, hi, huniq⟩ := h
      exact ⟨i, Ne.symm hi, fun j hj => huniq j (Ne.symm hj)⟩
  · intro h
    have hne : x ≠ y := by
      obtain ⟨i, hi, _⟩ := h
      exact fun heq => hi (congrFun heq i)
    exact ⟨hne, Or.inl h⟩

/-- `Q_0` has no edges: any two vertices agree on all (zero) coordinates. -/
theorem hypercubeGraph_zero_not_adj (x y : Fin 0 → Bool) :
    ¬ (hypercubeGraph 0).Adj x y := by
  rw [hypercubeGraph_adj]
  rintro ⟨i, _, _⟩
  exact Fin.elim0 i

/-- The canonical adjacent pair in `Q_1`: constant `true` and constant `false`. -/
theorem hypercubeGraph_one_adj :
    (hypercubeGraph 1).Adj (fun _ => true) (fun _ => false) := by
  rw [hypercubeGraph_adj]
  exact ⟨0, by simp, fun j _ => Subsingleton.elim j 0⟩

/-- `Q_0` has an empty edge set. -/
theorem hypercubeGraph_zero_edgeSet : (hypercubeGraph 0).edgeSet = ∅ := by
  rw [SimpleGraph.edgeSet_eq_empty]
  ext x y
  constructor
  · exact hypercubeGraph_zero_not_adj x y
  · intro h
    simp at h

/-- Every subgraph of `Q_n` has at most as many edges as `Q_n`. -/
theorem hypercubeGraph_subgraph_edgeSet_ncard_le (n : ℕ)
    (S : Subgraph (hypercubeGraph n)) :
    S.edgeSet.ncard ≤ (hypercubeGraph n).edgeSet.ncard :=
  Set.ncard_le_ncard S.edgeSet_subset (Set.toFinite _)

/-- The hypercube Turán number `ex(Q_n, H)`: the maximum edge count over all
`H`-free subgraphs of `Q_n`, as a total `Finset.sup` (zero when no witness exists). -/
noncomputable def hypercubeTuranNumber (n : ℕ) {W : Type*} (H : SimpleGraph W) : ℕ := by
  classical
  exact Finset.sup
    ((Finset.range ((hypercubeGraph n).edgeSet.ncard + 1)).filter
      (fun m => ∃ S : Subgraph (hypercubeGraph n), H.Free S.coe ∧ S.edgeSet.ncard = m))
    id

/-- Every `H`-free subgraph edge count is bounded by `ex(Q_n, H)`. -/
theorem le_hypercubeTuranNumber (n : ℕ) {W : Type*} {H : SimpleGraph W}
    (S : Subgraph (hypercubeGraph n)) (hfree : H.Free S.coe) :
    S.edgeSet.ncard ≤ hypercubeTuranNumber n H := by
  classical
  unfold hypercubeTuranNumber
  have hmem : S.edgeSet.ncard ∈
      ((Finset.range ((hypercubeGraph n).edgeSet.ncard + 1)).filter
        (fun m => ∃ S : Subgraph (hypercubeGraph n), H.Free S.coe ∧ S.edgeSet.ncard = m)) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hypercubeGraph_subgraph_edgeSet_ncard_le n S), S, hfree, rfl⟩
  have h := Finset.le_sup hmem (f := id)
  simpa using h

/-- `ex(Q_n, H)` is bounded by the edge count of `Q_n`. -/
theorem hypercubeTuranNumber_le_edgeSet_ncard (n : ℕ) {W : Type*} (H : SimpleGraph W) :
    hypercubeTuranNumber n H ≤ (hypercubeGraph n).edgeSet.ncard := by
  classical
  unfold hypercubeTuranNumber
  apply Finset.sup_le
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  obtain ⟨_, S, _, rfl⟩ := hm
  simpa using hypercubeGraph_subgraph_edgeSet_ncard_le n S

/-- When at least one `H`-free subgraph exists, the maximum is attained. -/
theorem exists_attains_hypercubeTuranNumber (n : ℕ) {W : Type*} {H : SimpleGraph W}
    (hne : ∃ S : Subgraph (hypercubeGraph n), H.Free S.coe) :
    ∃ S : Subgraph (hypercubeGraph n),
      H.Free S.coe ∧ S.edgeSet.ncard = hypercubeTuranNumber n H := by
  classical
  obtain ⟨S₀, hfree₀⟩ := hne
  have hmem₀ : S₀.edgeSet.ncard ∈
      ((Finset.range ((hypercubeGraph n).edgeSet.ncard + 1)).filter
        (fun m => ∃ S : Subgraph (hypercubeGraph n),
          H.Free S.coe ∧ S.edgeSet.ncard = m)) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hypercubeGraph_subgraph_edgeSet_ncard_le n S₀), S₀, hfree₀, rfl⟩
  have hne' : (((Finset.range ((hypercubeGraph n).edgeSet.ncard + 1)).filter
      (fun m => ∃ S : Subgraph (hypercubeGraph n),
        H.Free S.coe ∧ S.edgeSet.ncard = m)) : Finset ℕ).Nonempty :=
    ⟨_, hmem₀⟩
  obtain ⟨m, hm, hsup⟩ := Finset.exists_mem_eq_sup _ hne' (id : ℕ → ℕ)
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  obtain ⟨_, S, hfree, rfl⟩ := hm
  exact ⟨S, hfree, hsup.symm⟩

/-- Boundary value: the extremal number over `Q_0` is zero. -/
theorem hypercubeTuranNumber_zero {W : Type*} (H : SimpleGraph W) :
    hypercubeTuranNumber 0 H = 0 := by
  have h := hypercubeTuranNumber_le_edgeSet_ncard 0 H
  rw [hypercubeGraph_zero_edgeSet, Set.ncard_empty] at h
  exact Nat.le_zero.mp h

end SimpleGraph
