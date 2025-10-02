import sympy.vector.vector
import sympy.Basic


@[main]
private lemma main
  [Div α]
-- given
  (h : n = n')
  (a b : List.Vector α n) :
-- imply
  have h : List.Vector α n = List.Vector α n' := by rw [h]
  cast h (a / b) = cast h a / cast h b := by
-- proof
  aesop


@[main]
private lemma scalar
  [Div α]
-- given
  (h : n = n')
  (a : List.Vector α n)
  (c : α) :
-- imply
  have h : List.Vector α n = List.Vector α n' := by rw [h]
  cast h (a / c) = cast h a / c := by
-- proof
  aesop


-- created on 2025-09-21
