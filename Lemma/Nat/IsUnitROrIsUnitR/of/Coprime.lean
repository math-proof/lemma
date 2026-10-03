import Mathlib
import sympy.Basic


/--
[IsLocalRing_isUnit_natCast_or_isUnit_natCast_of_coprime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_isUnit_natCast_or_isUnit_natCast_of_coprime.lean)
-/
@[main]
private lemma main
  [CommRing R] [IsLocalRing R]
  {m n : ℕ}
-- given
  (h : Nat.Coprime m n) :
-- imply
  IsUnit (m : R) ∨ IsUnit (n : R) := by
-- proof
  obtain ⟨u, v, huv⟩ := Nat.Coprime.cast (R := R) h
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (huv ▸ isUnit_one) with hu | hv
  · exact Or.inl (isUnit_of_mul_isUnit_right hu)
  · exact Or.inr (isUnit_of_mul_isUnit_right hv)


-- created on 2026-10-03
