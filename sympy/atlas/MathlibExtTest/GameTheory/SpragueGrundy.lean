/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GameTheory/SpragueGrundy.lean -/


import sympy.atlas.GameTheory.SpragueGrundy
import Lemma.Set.SpragueGrundy

namespace MetaMathlibExt.SpragueGrundy

-- Terminal position: the empty heap has no moves, so it is a P-position.
example : IsP (nimHeap 0) (nimHeap 0).start :=
  (isP_iff _ _).mpr fun _ hq => absurd (Finset.mem_filter.mp hq).2 (Nat.not_lt_zero _)

-- Nonterminal position: a heap of size one moves to the empty heap, a P-position.
example : ¬ IsP (nimHeap 1) (nimHeap 1).start := by
  have h0 : IsP (nimHeap 1) (0 : Fin 2) :=
    (isP_iff _ _).mpr fun _ hq => absurd (Finset.mem_filter.mp hq).2 (Nat.not_lt_zero _)
  rw [isP_iff]
  exact fun h => h (0 : Fin 2)
    (by decide : (0 : Fin 2) ∈ Finset.univ.filter fun j : Fin 2 => j.val < 1) h0

end MetaMathlibExt.SpragueGrundy
