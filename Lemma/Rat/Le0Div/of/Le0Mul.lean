import Lemma.Rat.Div.eq.Mul_Inv
import Lemma.Int.Le0Mul.is.AndGeS_0.ou.AndLeS_0
open Int Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h : x * y ≥ 0) :
-- imply
  x / y ≥ 0 := by
-- proof
  -- Use the property that the product of two elements is non-negative if and only if both are non-negative or both are non-positive.
  rw [Div.eq.Mul_Inv]
  -- Split the proof into two cases based on the signs of x and y.
  obtain hx | hx := le_total 0 x <;>
  ·
    obtain hy | hy := le_total 0 y <;>
    ·
      obtain hy_inv | hy_inv := le_total 0 y⁻¹ <;>
      ·
        simp_all [Le0Mul.is.AndGeS_0.ou.AndLeS_0]


-- created on 2025-03-23
