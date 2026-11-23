/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

module

public import Mathlib.Data.Fintype.Card
public import Instance.Order.StrictTotalOrder
public import Theorem.Set.StrictTotalOrder
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Theorem.Combinatorics.Matching.GaleShapley.Part2

@[expose] public section

/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

noncomputable def womanChoice {M : Type*}
    (T : StrictTotalOrder M) (o : Option M) (m : M) : M :=
  Classical.choose (womanChoice_exists T o m)

end MathlibExt.Combinatorics.Matching.GaleShapley
