/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

import Mathlib.Data.Fintype.Card
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Structure.Combinatorics.Matching.GaleShapley
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-- A man is free if no woman holds him. -/
def DAState.Free {M W : Type*} (s : DAState M W) (m : M) : Prop :=
  ∀ w, s.hold w ≠ some m

/-- A man can propose if he is free and has not proposed to every woman. -/
def DAState.CanPropose {M W : Type*} (s : DAState M W) (m : M) : Prop :=
  s.Free m ∧ ∃ w, w ∉ s.prop m

/-- No man can propose. -/
def DAState.Done {M W : Type*} (s : DAState M W) : Prop :=
  ∀ m, ¬ s.CanPropose m

end MathlibExt.Combinatorics.Matching.GaleShapley
