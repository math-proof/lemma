/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

import Mathlib.Data.Fintype.Card
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Def.Combinatorics.Matching.GaleShapley.Part5
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-- The remaining-proposal set of the chosen man is nonempty. -/
lemma dastepNe {M W : Type*} [Fintype W] [DecidableEq W]
    (_mp : MPrefs M W) (s : DAState M W) (h : ∃ m, s.CanPropose m) :
    (Finset.univ.filter (fun w => w ∉ s.prop (Classical.choose h))).Nonempty := by
  obtain ⟨_hmfree, w, hw⟩ := Classical.choose_spec h
  exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩⟩

end MathlibExt.Combinatorics.Matching.GaleShapley
