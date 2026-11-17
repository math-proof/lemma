module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.LtAddS.is.Lt |
| comm | Nat.Lt.is.LtAddS |
| mp 4 | Nat.Lt.of.LtAddS |
| mpr 8 | Nat.LtAddS.of.Lt |
| mp.comm 4| Nat.Gt.of.GtAddS |
| mpr.comm 8| Nat.GtAddS.of.Gt |
| comm.is | Nat.GtAddS.is.Gt |
-/
@[comm, mp 4, mpr 8, mp.comm 4, mpr.comm 8, comm.is]
public theorem Nat.LtAddS.is.Lt
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
  ⟨lt_of_add_lt_add_right, (add_lt_add_left · a)⟩


@[comm, mp 4, mpr 8, mp.comm 4, mpr.comm 8, comm.is]
public theorem left
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
  ⟨lt_of_add_lt_add_left, (add_lt_add_right · a)⟩


-- created on 2018-10-10
