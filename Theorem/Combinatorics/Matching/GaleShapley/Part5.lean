module
public import Mathlib.Data.Fintype.Card
public import Instance.Order.StrictTotalOrder
public import Theorem.Set.StrictTotalOrder
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Def.Combinatorics.Matching.GaleShapley.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/
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
