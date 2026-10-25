/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CubicLatticeColoredMotzkin.lean -/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Def.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR.Part2
import Lemma.Finset.Enumerative.ULDMotzkinNumberOfRankR
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum


namespace MetaMathlibExt

/-- Flat color index for a non-distinguished cubic-lattice step. -/
def flatIndex (n : ℕ) (x : Fin (n + 1) × Bool) (h : ¬x.1 = Fin.last n) :
    Fin (2 * n) :=
  ⟨x.1.val * 2 + (if x.2 then 1 else 0), by
    have hlt : x.1.val < n + 1 := x.1.isLt
    have hne : x.1.val ≠ n := by
      intro he
      apply h
      rw [Fin.ext_iff, Fin.val_last]
      exact he
    have hb : (if x.2 then (1 : ℕ) else 0) ≤ 1 := by
      cases x.2
      · simp
      · simp
    have hv : x.1.val < n := by omega
    omega⟩

end MetaMathlibExt
