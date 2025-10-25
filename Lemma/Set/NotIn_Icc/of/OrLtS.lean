import sympy.sets.sets
import Lemma.Nat.NotLt.of.Ge
open Nat


@[main]
private lemma main
  [Preorder α]
  {e a b : α}
-- given
  (h : (e < a) ∨ (b < e)) :
-- imply
  e ∉ Icc a b := by
-- proof
  contrapose! h
  let ⟨ha, hb⟩ := h
  constructor <;>
  ·
    apply NotLt.of.Ge
    assumption


-- created on 2025-08-15
