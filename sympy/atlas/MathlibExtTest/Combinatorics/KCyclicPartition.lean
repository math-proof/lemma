/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/KCyclicPartition.lean -/


import sympy.atlas.Combinatorics.KCyclicPartition
import Mathlib.Logic.Equiv.Fin.Rotate

open Equiv
open Equiv.Perm
open Fin

#check @MetaMathlibExt.TruncatedSucc
#check @MetaMathlibExt.IsKCyclicPartition

-- Boundary: the truncated successor of the identity permutation at `i` is `i`.
example (i : Fin 3) : MetaMathlibExt.TruncatedSucc (1 : Equiv.Perm (Fin 3)) i i := by
  refine ⟨1, by omega, le_rfl, by simp, ?_⟩
  intro m' hm' hlt
  have hFalse : False := by omega
  exact False.elim hFalse

-- Boundary: the total cycle count of the identity is the carrier cardinality.
example : (1 : Equiv.Perm (Fin 3)).cycleType.card +
    (Fintype.card (Fin 3) - (1 : Equiv.Perm (Fin 3)).support.card) =
    Fintype.card (Fin 3) := by
  simp

-- Boundary: the identity satisfies the k-cyclic predicate with the empty edge relation.
example : MetaMathlibExt.IsKCyclicPartition (1 : Equiv.Perm (Fin 3))
    (fun _ _ => False) (Fintype.card (Fin 3)) := by
  refine ⟨by simp, ?_⟩
  intro i j _ h
  exact h

-- Boundary: nontrivial cycle where forward traversal from `1` first visits `2 > 1`
-- then returns to `0 ≤ 1`, so the exact truncated successor is `0`.
example : MetaMathlibExt.TruncatedSucc (finCycle (1 : Fin 3)) 1 0 := by
  refine ⟨2, by omega, by decide, by decide, ?_⟩
  intro m' hm' hlt
  have hm1 : m' = 1 := by omega
  subst hm1
  decide

-- Exclusion: `2` is not the truncated successor at `1` since `2 ≤ 1` is false.
example : ¬ MetaMathlibExt.TruncatedSucc (finCycle (1 : Fin 3)) 1 2 := by
  intro h
  obtain ⟨m, hm, hle, heq, hfirst⟩ := h
  exact (by decide : ¬ ((2 : Fin 3) ≤ 1)) hle
