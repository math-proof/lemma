import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.MaxFlowMenger
open Finset StatMech StatMech.Combinatorics


/--
[mfm_separator_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxFlowMenger.lean)
-/
@[path]
private lemma mfm_separator_mono_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {H : SimpleGraph V}
  {A B S : Finset V}
-- given
  (h : H ≤ G)
  (hS : MfmIsABSeparator G A B S) :
-- imply
  MfmIsABSeparator H A B S := by
-- proof
  apply StatMech.Combinatorics.mfm_separator_mono h hS

/--
[mfm_card_le_separator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxFlowMenger.lean)
-/
@[path]
private lemma mfm_card_le_separator_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset V}
  {n : ℕ}
  {L : MfmLinkage G A B n}
  {S : Finset V}
-- given
  (hS : MfmIsABSeparator G A B S) :
-- imply
  n ≤ S.card := by
-- proof
  apply StatMech.Combinatorics.mfm_card_le_separator L hS

/--
[mfm_separator_nonempty_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxFlowMenger.lean)
-/
@[path]
private lemma mfm_separator_nonempty_of_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B S : Finset V}
  {a b : V}
-- given
  (hS : MfmIsABSeparator G A B S)
  (ha : a ∈ A)
  (hb : b ∈ B)
  (h : G.Reachable a b) :
-- imply
  S.Nonempty := by
-- proof
  apply StatMech.Combinatorics.mfm_separator_nonempty_of_reachable hS ha hb h

/--
[mfm_isABSeparator_empty_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxFlowMenger.lean)
-/
@[path]
private lemma mfm_isABSeparator_empty_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset V} :
-- imply
  MfmIsABSeparator G A B ∅ ↔ ∀ a ∈ A, ∀ b ∈ B, ¬ G.Reachable a b := by
-- proof
  apply StatMech.Combinatorics.mfm_isABSeparator_empty_iff

/--
[mfm_exists_linkage_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxFlowMenger.lean)
-/
@[path]
private lemma mfm_exists_linkage_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset V}
-- given
  (h : ∀ S : Finset V, MfmIsABSeparator G A B S → 1 ≤ S.card) :
-- imply
  Nonempty (MfmLinkage G A B 1) := by
-- proof
  apply StatMech.Combinatorics.mfm_exists_linkage_one h


-- created on 2026-10-23
