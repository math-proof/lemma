import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Saturation
open SimpleGraph


/--
[isSaturated_def](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Saturation.lean)
-/
@[path]
private lemma isSaturated_def_eq
  {H : SimpleGraph V}
  {G : SimpleGraph W} :
-- imply
  H.IsSaturated G ↔ H.Free G ∧ ∀ ⦃G' : SimpleGraph W⦄, H.Free G' → G ≤ G' → G' ≤ G := by
-- proof
  apply SimpleGraph.isSaturated_def H G

/--
[isSaturated_iff_forall_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Saturation.lean)
-/
@[path]
private lemma isSaturated_iff_forall_gt_eq
  {H : SimpleGraph V}
  {G : SimpleGraph W} :
-- imply
  H.IsSaturated G ↔ H.Free G ∧ ∀ ⦃G' : SimpleGraph W⦄, G < G' → ¬ H.Free G' := by
-- proof
  apply SimpleGraph.isSaturated_iff_forall_gt H G

/--
[isSaturated_iff_missing_edge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Saturation.lean)
-/
@[path]
private lemma isSaturated_iff_missing_edge_eq
  {H : SimpleGraph V}
  {G : SimpleGraph W} :
-- imply
  H.IsSaturated G ↔
    H.Free G ∧ ∀ s t : W, s ≠ t → ¬ G.Adj s t → ¬ H.Free (G ⊔ edge s t) := by
-- proof
  apply SimpleGraph.isSaturated_iff_missing_edge H G

/--
[isSaturated_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Saturation.lean)
-/
@[path]
private lemma isSaturated_top_eq
  {H : SimpleGraph V} :
-- imply
  H.IsSaturated (⊤ : SimpleGraph W) ↔ H.Free (⊤ : SimpleGraph W) := by
-- proof
  apply SimpleGraph.isSaturated_top H

/--
[sat_eq_zero_of_counts_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Saturation.lean)
-/
@[path]
private lemma sat_eq_zero_of_counts_empty_eq
  {H : SimpleGraph V}
  {n : ℕ}
-- given
  (h : H.satCounts n = ∅) :
-- imply
  H.sat n = 0 := by
-- proof
  apply SimpleGraph.sat_eq_zero_of_counts_empty H n h

/--
[sat_le_card_of_isSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Saturation.lean)
-/
@[path]
private lemma sat_le_card_of_isSaturated_eq
  {H : SimpleGraph V}
  {n : ℕ}
  {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
-- given
  (h : H.IsSaturated G) :
-- imply
  H.sat n ≤ G.edgeFinset.card := by
-- proof
  apply SimpleGraph.sat_le_card_of_isSaturated H n G h

/--
[exists_isSaturated_card_eq_sat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Saturation.lean)
-/
@[path]
private lemma exists_isSaturated_card_eq_sat_eq
  {H : SimpleGraph V}
  {n : ℕ}
-- given
  (h : (H.satCounts n).Nonempty) :
-- imply
  ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj, H.IsSaturated G ∧
    G.edgeFinset.card = H.sat n := by
-- proof
  apply SimpleGraph.exists_isSaturated_card_eq_sat H n h


-- created on 2026-10-20
