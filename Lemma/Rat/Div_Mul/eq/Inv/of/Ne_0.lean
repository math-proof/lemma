import Lemma.Rat.DivDiv.eq.Div_Mul
import Lemma.Nat.Mul
open Rat Nat


private lemma inv'
  [CommGroupWithZero α]
  {a b : α}
-- given
  (h : a ≠ 0) :
-- imply
  a / (a * b) = b⁻¹ := by
-- proof
  rw [Div_Mul.eq.DivDiv]
  simp [h]


@[main]
private lemma main
  [CommGroupWithZero α]
  {a b : α}
-- given
  (h : a ≠ 0)
  (comm : Bool := false) :
-- imply
  match comm with
  | true =>
    a / (b * a) = b⁻¹
  | false =>
    a / (a * b) = b⁻¹ := by
-- proof
  match comm with
  | true =>
    simp
    rw [Mul.comm]
    apply inv' h
  | false =>
    simp
    apply inv' h


-- created on 2024-07-01
-- updated on 2025-04-07
