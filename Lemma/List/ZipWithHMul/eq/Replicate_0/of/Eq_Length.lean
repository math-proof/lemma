import sympy.Basic


@[main]
private lemma main
  [MulZeroClass α]
  {s : List α}
-- given
  (h : l = s.length) :
-- imply
  List.zipWith HMul.hMul (List.replicate l 0) s = List.replicate l 0 := by
-- proof
  induction s generalizing l with
  | nil =>
    simp_all
  | cons head tail ih =>
    cases l <;>
      simp_all [List.replicate]


-- created on 2025-05-02
