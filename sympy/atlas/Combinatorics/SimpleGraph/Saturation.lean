/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Saturation.lean -/

-- MathlibExt/Combinatorics/SimpleGraph/Saturation.lean

import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Minimal

/-!
# Graph saturation and the saturation number

Source: Huanying Bian, Qing Cui, Shengjin Ji, and Fuhong Ma,
*On the saturation number of the kite graph*, arXiv:2608.16069v1.

For a fixed graph `H`, a graph `G` is `H`-saturated if `G` does not contain a
copy of `H`, but for any edge `e` not in `E(G)`, the graph `G + e` contains a
copy of `H`. The saturation number `sat(n, H)` is the minimum size of an
`H`-saturated graph on `n` vertices.

Representation: `H`-saturation is maximal `H`-freeness (`Maximal H.Free G`) in
the graph-inclusion order, with the equivalence to the source's missing-edge
formulation proved below. `sat` is the infimum of edge counts over saturated
graphs on `Fin n`; it equals `0` when no saturated graph exists.
-/

namespace SimpleGraph

variable {V W : Type*} (H : SimpleGraph V)

/-- `H`-saturation: `G` is `H`-free and maximal with that property in the
graph-inclusion order. -/
def IsSaturated (G : SimpleGraph W) : Prop :=
  Maximal H.Free G

theorem isSaturated_def (G : SimpleGraph W) :
    H.IsSaturated G ↔ H.Free G ∧ ∀ ⦃G' : SimpleGraph W⦄, H.Free G' → G ≤ G' → G' ≤ G :=
  Iff.rfl

/-- Maximality unfolded with strict extensions. -/
theorem isSaturated_iff_forall_gt (G : SimpleGraph W) :
    H.IsSaturated G ↔ H.Free G ∧ ∀ ⦃G' : SimpleGraph W⦄, G < G' → ¬ H.Free G' :=
  maximal_iff_forall_gt

/-- Equivalence with the source's missing-edge formulation: `G` is `H`-saturated
iff it is `H`-free and every one-edge extension contains a copy of `H`. -/
theorem isSaturated_iff_missing_edge (G : SimpleGraph W) :
    H.IsSaturated G ↔
      H.Free G ∧ ∀ s t : W, s ≠ t → ¬ G.Adj s t → ¬ H.Free (G ⊔ edge s t) := by
  rw [isSaturated_iff_forall_gt]
  constructor
  · rintro ⟨hfree, hall⟩
    exact ⟨hfree, fun s t hne hmiss => hall (G.lt_sup_edge s t hne hmiss)⟩
  · rintro ⟨hfree, hall⟩
    refine ⟨hfree, fun G' hlt hfree' => ?_⟩
    obtain ⟨hle, hne⟩ := lt_iff_le_not_ge.mp hlt
    rw [le_iff_adj] at hle hne
    push Not at hne
    obtain ⟨s, t, hadj', hadj⟩ := hne
    have hst : s ≠ t := G'.ne_of_adj hadj'
    have hle2 : G ⊔ edge s t ≤ G' := sup_le hle ((edge_le_iff (G := G')).mpr (Or.inr hadj'))
    exact hfree' ((not_free.mp (hall s t hst hadj)).mono_right hle2)

/-- A complete host has no missing edge, so it is saturated exactly when it is
`H`-free. The host lives on its own vertex type, so this is meaningful: a
forbidden graph need not embed in a complete host with fewer vertices. -/
theorem isSaturated_top : H.IsSaturated (⊤ : SimpleGraph W) ↔ H.Free (⊤ : SimpleGraph W) := by
  constructor
  · exact fun h => h.1
  · intro h
    exact maximal_iff_forall_gt.mpr ⟨h, fun _ hlt => absurd hlt not_top_lt⟩

/-- Edge counts of `H`-saturated graphs on `Fin n`. -/
def satCounts (n : ℕ) : Set ℕ :=
  { m | ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj, H.IsSaturated G ∧
    G.edgeFinset.card = m }

/-- The saturation number `sat(n, H)`: the minimum size of an `H`-saturated
graph on `n` vertices. This is `0` when no saturated graph exists. -/
noncomputable def sat (n : ℕ) : ℕ :=
  sInf (H.satCounts n)

/-- Explicit total value on the empty admissible family. -/
theorem sat_eq_zero_of_counts_empty (n : ℕ) (h : H.satCounts n = ∅) : H.sat n = 0 := by
  change sInf (H.satCounts n) = 0
  rw [h, Nat.sInf_empty]

/-- Upper bound: `sat(n, H)` is at most the edge count of any saturated graph. -/
theorem sat_le_card_of_isSaturated (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h : H.IsSaturated G) :
    H.sat n ≤ G.edgeFinset.card := by
  change sInf (H.satCounts n) ≤ _
  refine csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ ?_
  change ∃ G' : SimpleGraph (Fin n), ∃ _ : DecidableRel G'.Adj,
    H.IsSaturated G' ∧ G'.edgeFinset.card = G.edgeFinset.card
  exact ⟨G, inferInstance, h, rfl⟩

/-- Attainment: when a saturated graph exists, some saturated graph has exactly
`sat(n, H)` edges. -/
theorem exists_isSaturated_card_eq_sat (n : ℕ) (h : (H.satCounts n).Nonempty) :
    ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj, H.IsSaturated G ∧
      G.edgeFinset.card = H.sat n := by
  obtain ⟨G, hdec, hsat, hcard⟩ := Nat.sInf_mem h
  exact ⟨G, hdec, hsat, hcard⟩

end SimpleGraph
