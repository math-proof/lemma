import Lemma.Nat.Ge.of.NotLt
import Lemma.List.GetElem.eq.None.of.Ge_Length
open List Nat


@[main]
private lemma main
-- given
  (s : List α)
  (a : α)
  (i : ℕ) :
-- imply
  s[i]? = some a ↔ ∃ h : i < s.length, s[i] = a := by
-- proof
  by_cases hi : i < s.length <;>
    simp [hi]


-- created on 2025-05-10
