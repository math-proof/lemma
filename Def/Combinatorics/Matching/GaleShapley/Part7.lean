/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

import Mathlib.Data.Fintype.Card
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Theorem.Combinatorics.Matching.GaleShapley.Part6
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-- Initial state: no proposals, no holders. -/
def dainit {M W : Type*} : DAState M W :=
  { prop := fun _ => ∅, hold := fun _ => none }

/-- Run the algorithm for `n` steps (stopping early once done). -/
noncomputable def darun {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M]
    [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) : ℕ → DAState M W → DAState M W
  | 0, s => s
  | n + 1, s =>
    @dite _ _ (Classical.propDecidable _) (fun h : ∃ m, s.CanPropose m =>
      darun mp wp n (dastep mp wp s h)) (fun _ => s)

end MathlibExt.Combinatorics.Matching.GaleShapley
