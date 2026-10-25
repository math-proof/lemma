/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

import Mathlib.Data.Fintype.Card
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Def.Combinatorics.Matching.GaleShapley
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-! ## Proof of Gale–Shapley via the men-proposing deferred-acceptance algorithm.

State: each man records the women he proposed to (`prop`); each woman holds her best
proposer so far (`hold`). A free man who has not proposed everywhere proposes to his
favourite remaining woman; she keeps the better of her old holder and the new proposer.
The number of proposals strictly grows each step and is bounded by `|M| * |W|`, so after
`K = |M| * |W| + 1` steps no man can propose; that state yields a stable matching. -/

/-- A nonempty finset has a strictly-least element under a strict total order. -/
lemma sto_exists_minimal {α : Type*} (T : StrictTotalOrder α) :
    ∀ (s : Finset α), s.Nonempty → ∃ x ∈ s, ∀ y ∈ s, x ≠ y → T.lt x y := by
  classical
  intro s
  induction s using Finset.induction
  case empty =>
    intro h
    exact (Finset.not_nonempty_empty h).elim
  case insert a s _ha ih =>
    intro h
    by_cases hs : s.Nonempty
    · obtain ⟨x, hxs, hmin⟩ := ih hs
      by_cases hax : a = x
      · refine ⟨x, Finset.mem_insert_of_mem hxs, fun y hy hne => ?_⟩
        rcases Finset.mem_insert.mp hy with rfl | hys
        · exact absurd hax.symm hne
        · exact hmin y hys hne
      · rcases T.total hax with hlt | hlt
        · refine ⟨a, Finset.mem_insert_self a s, fun y hy hne => ?_⟩
          rcases Finset.mem_insert.mp hy with rfl | hys
          · exact absurd rfl hne
          · by_cases hyx : y = x
            · subst hyx
              exact hlt
            · exact T.trans hlt (hmin y hys (Ne.symm hyx))
        · refine ⟨x, Finset.mem_insert_of_mem hxs, fun y hy hne => ?_⟩
          rcases Finset.mem_insert.mp hy with rfl | hys
          · exact hlt
          · exact hmin y hys hne
    · have hsempty : s = ∅ :=
        Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => hs ⟨x, hx⟩)
      refine ⟨a, Finset.mem_insert_self a s, fun y hy hne => ?_⟩
      rcases Finset.mem_insert.mp hy with rfl | hys
      · exact absurd rfl hne
      · rw [hsempty] at hys
        exact (Finset.notMem_empty y hys).elim

end MathlibExt.Combinatorics.Matching.GaleShapley
