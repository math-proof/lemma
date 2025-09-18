import Lemma.Algebra.ModAddMul.eq.Mod
import Lemma.Algebra.ModAdd_Mul.eq.Mod
open Algebra


@[main]
private lemma main
  [IntegerRing Z]
  {y d : Z}
-- given
  (h : d ∣ y)
  (x : Z) :
-- imply
  (x + y) % d = x % d := by
-- proof
  obtain ⟨k, h⟩ := h
  rw [h]
  rw [ModAdd_Mul.eq.Mod.left]


@[main]
private lemma left
  [IntegerRing Z]
  {x d : Z}
-- given
  (h : d ∣ x)
  (y : Z) :
-- imply
  (x + y) % d = y % d := by
-- proof
  obtain ⟨k, h⟩ := h
  rw [h]
  rw [ModAddMul.eq.Mod.left]


-- created on 2025-07-08
