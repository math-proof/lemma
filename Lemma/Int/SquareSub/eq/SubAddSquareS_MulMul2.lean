import Lemma.Nat.SquareAdd.eq.AddAddSquareS_MulMul2
import Lemma.Int.Sub.eq.Add_Neg
open Int Nat


@[main]
private lemma main
  [CommRing α]
-- given
  (a b : α) :
-- imply
  (a - b)² = a² + b² - 2 * a * b := by
-- proof
  rw [
    Sub.eq.Add_Neg,
    SquareAdd.eq.AddAddSquareS_MulMul2
  ]
  simp [Sub.eq.Add_Neg]


-- created on 2024-07-01
