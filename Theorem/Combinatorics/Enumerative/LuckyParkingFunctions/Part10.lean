/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.LuckyParkingFunctions.Part9


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
