module
public import Mathlib.Data.Fintype.Card
public import Instance.Order.StrictTotalOrder
public import Theorem.Set.StrictTotalOrder
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Theorem.Combinatorics.Matching.GaleShapley.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/
namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-- One algorithm step: the chosen free man proposes to his favourite remaining woman. -/
noncomputable def dastep {M W : Type*} [Fintype W] [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W)
    (h : ∃ m, s.CanPropose m) : DAState M W :=
  dostep mp wp s (Classical.choose h)
    (Classical.choose (sto_exists_minimal (mp (Classical.choose h))
      (Finset.univ.filter (fun w => w ∉ s.prop (Classical.choose h)))
      (dastepNe mp s h)))

end MathlibExt.Combinatorics.Matching.GaleShapley
