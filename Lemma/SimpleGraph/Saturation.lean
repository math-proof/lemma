import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.SimpleGraph.Saturation
open SimpleGraph


namespace SimpleGraph

/--
[isSaturated_def](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Saturation.lean)
-/
@[path]
lemma isSaturated_def
  {H : SimpleGraph V}
  {G : SimpleGraph W} :
-- imply
  H.IsSaturated G ↔ H.Free G ∧ ∀ ⦃G' : SimpleGraph W⦄, H.Free G' → G ≤ G' → G' ≤ G :=
-- proof
  Iff.rfl

end SimpleGraph

namespace SimpleGraph

/--
[isSaturated_iff_forall_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Saturation.lean)
-/
@[path]
lemma isSaturated_iff_forall_gt
  {H : SimpleGraph V}
  {G : SimpleGraph W} :
-- imply
  H.IsSaturated G ↔ H.Free G ∧ ∀ ⦃G' : SimpleGraph W⦄, G < G' → ¬ H.Free G' :=
-- proof
  maximal_iff_forall_gt

end SimpleGraph

namespace SimpleGraph

/--
[isSaturated_iff_missing_edge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Saturation.lean)
-/
@[path]
lemma isSaturated_iff_missing_edge
  {H : SimpleGraph V}
  {G : SimpleGraph W} :
-- imply
  H.IsSaturated G ↔
    H.Free G ∧ ∀ s t : W, s ≠ t → ¬ G.Adj s t → ¬ H.Free (G ⊔ edge s t) := by
-- proof
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

end SimpleGraph

namespace SimpleGraph

/--
[isSaturated_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Saturation.lean)
-/
@[path]
lemma isSaturated_top
  {H : SimpleGraph V} :
-- imply
  H.IsSaturated (⊤ : SimpleGraph W) ↔ H.Free (⊤ : SimpleGraph W) := by
-- proof
  constructor
  · exact fun h => h.1
  · intro h
    exact maximal_iff_forall_gt.mpr ⟨h, fun _ hlt => absurd hlt not_top_lt⟩

end SimpleGraph

namespace SimpleGraph

/--
[sat_eq_zero_of_counts_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Saturation.lean)
-/
@[path]
lemma sat_eq_zero_of_counts_empty
  {H : SimpleGraph V}
  {n : ℕ}
-- given
  (h : H.satCounts n = ∅) :
-- imply
  H.sat n = 0 := by
-- proof
  change sInf (H.satCounts n) = 0
  rw [h, Nat.sInf_empty]

end SimpleGraph

namespace SimpleGraph

/--
[sat_le_card_of_isSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Saturation.lean)
-/
@[path]
lemma sat_le_card_of_isSaturated
  {H : SimpleGraph V}
  {n : ℕ}
  {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
-- given
  (h : H.IsSaturated G) :
-- imply
  H.sat n ≤ G.edgeFinset.card := by
-- proof
  change sInf (H.satCounts n) ≤ _
  refine csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ ?_
  change ∃ G' : SimpleGraph (Fin n), ∃ _ : DecidableRel G'.Adj,
    H.IsSaturated G' ∧ G'.edgeFinset.card = G.edgeFinset.card
  exact ⟨G, inferInstance, h, rfl⟩

end SimpleGraph

namespace SimpleGraph

/--
[exists_isSaturated_card_eq_sat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Saturation.lean)
-/
@[path]
lemma exists_isSaturated_card_eq_sat
  {H : SimpleGraph V}
  {n : ℕ}
-- given
  (h : (H.satCounts n).Nonempty) :
-- imply
  ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj, H.IsSaturated G ∧
    G.edgeFinset.card = H.sat n := by
-- proof
  obtain ⟨G, hdec, hsat, hcard⟩ := Nat.sInf_mem h
  exact ⟨G, hdec, hsat, hcard⟩

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-26
