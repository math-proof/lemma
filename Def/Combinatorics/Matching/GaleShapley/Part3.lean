/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

import Mathlib.Data.Fintype.Card
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Theorem.Combinatorics.Matching.GaleShapley.Part2
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

noncomputable def womanChoice {M : Type*}
    (T : StrictTotalOrder M) (o : Option M) (m : M) : M :=
  Classical.choose (womanChoice_exists T o m)

end MathlibExt.Combinatorics.Matching.GaleShapley
