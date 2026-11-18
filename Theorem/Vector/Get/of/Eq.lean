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



public theorem Vector.Get.of.Eq.fin
  {a b : List.Vector α n}
  (h : a = b)
  (i : ℕ)
  (hi : i < n) :
  a[i] = b[i] := by
  rw [h]

-- created on 2025-09-23
