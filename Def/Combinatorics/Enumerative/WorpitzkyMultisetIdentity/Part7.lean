module
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Sym.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Multiset.Count
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Data.Fintype.Fin
public import Abbrev.Combinatorics.Enumerative.WorpitzkyMultisetIdentity


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
