/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

module

public import Mathlib.Data.Fintype.Card
public import Instance.Order.StrictTotalOrder
public import Theorem.Set.StrictTotalOrder
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Abbrev.Combinatorics.Matching.GaleShapley.Part2

@[expose] public section

/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-- Blocking pair: `m` prefers `w` over `μ m` and `w` prefers `m` over `μ.symm w`. -/
def IsBlockingPair {M W : Type*}
    (mp : MPrefs M W) (wp : WPrefs M W) (μ : PerfectMatching M W) (m : M) (w : W) : Prop :=
  (mp m).lt w (μ m) ∧ (wp w).lt m (μ.symm w)

/-- A perfect matching is stable if it has no blocking pair. -/
def IsStable {M W : Type*} (mp : MPrefs M W) (wp : WPrefs M W) (μ : PerfectMatching M W) : Prop :=
  ∀ m w, ¬ IsBlockingPair mp wp μ m w

end MathlibExt.Combinatorics.Matching.GaleShapley
