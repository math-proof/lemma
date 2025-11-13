import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.LtAddS.is.Lt |
| comm | Nat.Lt.is.LtAddS |
| mp   | Nat.Lt.of.LtAddS |
| mpr  | Nat.LtAddS.of.Lt |
| mp.comm | Nat.Gt.of.GtAddS |
| mpr.comm | Nat.GtAddS.of.Gt |
| comm.is | Nat.GtAddS.is.Gt |
-/
@[main, comm, mp 4, mpr 8, mp.comm 4, mpr.comm 8, comm.is]
private lemma main
  [Add α]
  [LT α]
  [AddRightStrictMono α]
  [AddRightReflectLT α]
-- given
  (a x y : α) :
-- imply
  x + a < y + a ↔ x < y :=
-- proof
  -- add_lt_add_iff_right a
  ⟨lt_of_add_lt_add_right, (add_lt_add_right · a)⟩


@[main, comm, mp 4, mpr 8, mp.comm 4, mpr.comm 8, comm.is]
private lemma left
  [Add α]
  [LT α]
  [AddLeftStrictMono α]
  [AddLeftReflectLT α]
-- given
  (a x y : α) :
-- imply
  a + x < a + y ↔ x < y :=
-- proof
  -- add_lt_add_iff_left a
  ⟨lt_of_add_lt_add_left, (add_lt_add_left · a)⟩


-- created on 2025-08-02
