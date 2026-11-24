module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.LuckyParkingFunctions.Part9


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/
section

namespace MetaMathlibExt

lemma sumToPark_injective (n : ℕ) :
    Function.Injective (sumToPark n) := by
  intro x y hxy
  cases x with
  | inl a1 =>
    cases y with
    | inl a2 =>
      have ha : a1 = a2 := embedPlain_injective n (by
        simp only [sumToPark] at hxy
        exact hxy)
      rw [ha]
    | inr m2 =>
      have hcon : embedPlain n a1 = embedMarked n m2 := by
        simp only [sumToPark] at hxy
        exact hxy
      exact absurd hcon (embed_disjoint n a1 m2)
  | inr m1 =>
    cases y with
    | inl a2 =>
      have hcon : embedMarked n m1 = embedPlain n a2 := by
        simp only [sumToPark] at hxy
        exact hxy
      have hcon2 : embedPlain n a2 = embedMarked n m1 := hcon.symm
      exact absurd hcon2 (embed_disjoint n a2 m1)
    | inr m2 =>
      have hm : m1 = m2 := embedMarked_injective n (by
        simp only [sumToPark] at hxy
        exact hxy)
      rw [hm]

end MetaMathlibExt
end
