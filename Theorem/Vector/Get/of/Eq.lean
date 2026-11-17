module

public import Initialize.Tactic.Attr.Basic

public section


@[fin]
public theorem Vector.Get.of.Eq
  {a b : List.Vector α n}
-- given
  (h : a = b)
  (i : Fin n) :
-- imply
  a[i] = b[i] := by
-- proof
  rw [h]


-- created on 2025-09-23
