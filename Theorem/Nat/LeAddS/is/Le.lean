module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


@[comm, mp 8, mpr 4, mp.comm 8, mpr.comm 4, comm.is]
public theorem Nat.LeAddS.is.Le.left
  [Add α]
  [LE α]
  [AddLeftReflectLE α]
  [AddLeftMono α]
-- given
  (a b c : α) :
-- imply
  a + b ≤ a + c ↔ b ≤ c :=
-- proof
  ⟨le_of_add_le_add_left, (add_le_add_right · a)⟩


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.LeAddS.is.Le |
| comm | Nat.Le.is.LeAddS |
| mp 8 | Nat.Le.of.LeAddS |
| mpr 4| Nat.LeAddS.of.Le |
| mp.comm 8| Nat.Ge.of.GeAddS |
| mpr.comm 4| Nat.GeAddS.of.Ge |
| comm.is | Nat.GeAddS.is.Ge |
-/
@[comm, mp 8, mpr 4, mp.comm 8, mpr.comm 4, comm.is]
public theorem Nat.LeAddS.is.Le
  [Add α]
  [LE α]
  [AddRightReflectLE α]
  [AddRightMono α]
-- given
  (a b c : α) :
-- imply
  b + a ≤ c + a ↔ b ≤ c :=
-- proof
  ⟨le_of_add_le_add_right, (add_le_add_left · a)⟩



public theorem Nat.Le.of.LeAddS
  [Add α] [LE α] [AddRightReflectLE α] [AddRightMono α]
  {a b c : α}
  (h : b + a ≤ c + a) :
  b ≤ c :=
  (Nat.LeAddS.is.Le a b c).mp h

public theorem Nat.LeAddS.of.Le
  [Add α] [LE α] [AddRightMono α]
  {b c : α}
  (a : α)
  (h : b ≤ c) :
  b + a ≤ c + a :=
  add_le_add_left h a

public theorem Nat.LeAddS.of.Le.left
  [Add α] [LE α] [AddLeftMono α]
  {b c : α}
  (a : α)
  (h : b ≤ c) :
  a + b ≤ a + c :=
  add_le_add_right h a

-- created on 2018-02-25
