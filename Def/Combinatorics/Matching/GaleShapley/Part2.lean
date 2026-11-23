/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

module

public import Mathlib.Data.Fintype.Card
public import Instance.Order.StrictTotalOrder
public import Theorem.Set.StrictTotalOrder
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Structure.Combinatorics.Matching.GaleShapley

@[expose] public section

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
