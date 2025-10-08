import sympy.tensor.Basic
import Lemma.Rat.EqDivSDiv
open Rat


@[main]
private lemma main
  [DivisionCommMonoid α]
-- given
  (X : Tensor α s)
  (a b : α) :
-- imply
  X / a / b = X / b / a := by
-- proof
  simp [HDiv.hDiv]
  have h_fun : (fun x ↦ Div.div (Div.div x a) b) = (fun x ↦ (x / a) / b) := by
    simp [HDiv.hDiv]
  simp [h_fun]
  have h_fun : (fun x ↦ Div.div (Div.div x b) a) = (fun x ↦ (x / b) / a) := by
    simp [HDiv.hDiv]
  simp [h_fun]
  simp [EqDivSDiv]


-- created on 2025-09-26
