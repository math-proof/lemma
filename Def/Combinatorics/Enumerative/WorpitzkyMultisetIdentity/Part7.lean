/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Sym.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Fintype.Fin
import Abbrev.Combinatorics.Enumerative.WorpitzkyMultisetIdentity


section

namespace MetaMathlibExt

def wmiWordPairEquiv (m K x : ℕ) (k : Fin m → ℕ) :
    wmiWordData m K x k ≃ wmiPairData m K x k where
  toFun z :=
    ⟨fun j => toLex (z.2.1 j, z.1.1 j),
      (wmi_pair_monotone_iff z.1.1 z.2.1).2 z.2.2,
      fun i => by
        calc
          Fintype.card { j : Fin K //
              (ofLex (toLex (z.2.1 j, z.1.1 j))).2 = i } =
              Fintype.card { j : Fin K // z.1.1 j = i } := by
                apply Fintype.card_congr
                apply Equiv.subtypeEquivRight
                intro j
                simp
          _ = k i := z.1.2 i⟩
  invFun f :=
    ⟨⟨fun j => (ofLex (f.1 j)).2, f.2.2⟩,
      ⟨fun j => (ofLex (f.1 j)).1,
        (wmi_pair_monotone_iff _ _).1 f.2.1⟩⟩
  left_inv z := by
    rcases z with ⟨⟨w, hw⟩, ⟨e, he⟩⟩
    rfl
  right_inv f := by
    apply Subtype.ext
    funext j
    simp

end MetaMathlibExt
end
