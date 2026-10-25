/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

import Mathlib.Data.Fintype.Card
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Def.Combinatorics.Matching.GaleShapley.Part6
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-- Characterisation of the algorithm step. -/
lemma dastep_spec {M W : Type*} [Fintype W] [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W)
    (h : ∃ m, s.CanPropose m) :
    ∃ m0 w0, s.Free m0 ∧ w0 ∉ s.prop m0 ∧
      (∀ y, y ∉ s.prop m0 → w0 ≠ y → (mp m0).lt w0 y) ∧
      dastep mp wp s h = dostep mp wp s m0 w0 := by
  refine ⟨Classical.choose h,
    Classical.choose (sto_exists_minimal (mp (Classical.choose h))
      (Finset.univ.filter (fun w => w ∉ s.prop (Classical.choose h)))
      (dastepNe mp s h)), (Classical.choose_spec h).1, ?_, ?_, rfl⟩
  · exact (Finset.mem_filter.mp
      (Classical.choose_spec (sto_exists_minimal (mp (Classical.choose h))
        (Finset.univ.filter (fun w => w ∉ s.prop (Classical.choose h)))
        (dastepNe mp s h))).1).2
  · intro y hy hne
    exact (Classical.choose_spec (sto_exists_minimal (mp (Classical.choose h))
      (Finset.univ.filter (fun w => w ∉ s.prop (Classical.choose h)))
      (dastepNe mp s h))).2 y
      (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩) hne

lemma dastep_preserves {M W : Type*} [Fintype W] [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W)
    (h : ∃ m, s.CanPropose m) (hinv : DAInv mp wp s) :
    DAInv mp wp (dastep mp wp s h) := by
  obtain ⟨m0, w0, hfree, hnew, hfav, heq⟩ := dastep_spec mp wp s h
  rw [heq]
  exact dostep_preserves mp wp s m0 w0 hfree hnew hfav hinv

lemma dastep_measure {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W)
    (h : ∃ m, s.CanPropose m) :
    DAMeasure (dastep mp wp s h) = DAMeasure s + 1 := by
  obtain ⟨m0, w0, hfree, hnew, hfav, heq⟩ := dastep_spec mp wp s h
  rw [heq]
  exact dostep_measure mp wp s m0 w0 hnew

end MathlibExt.Combinatorics.Matching.GaleShapley
