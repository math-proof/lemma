import Lemma.Int.GeSquare_0
import Lemma.Int.Eq_0.and.Eq_0.of.Ge_0.Ge_0.Add.eq.Zero
import Lemma.Int.Eq_0.is.EqSquare_0
open Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h : x² + y² = 0) :
-- imply
  x = 0 ∧ y = 0 := by
-- proof
  have h_x := GeSquare_0 (a := x)
  have h_y := GeSquare_0 (a := y)
  have ⟨h_x, h_y⟩ := Eq_0.and.Eq_0.of.Ge_0.Ge_0.Add.eq.Zero h_x h_y h
  have := Eq_0.of.EqSquare_0 h_x
  have := Eq_0.of.EqSquare_0 h_y
  constructor <;> assumption


-- created on 2025-01-17
-- updated on 2025-01-26
