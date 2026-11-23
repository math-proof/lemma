module

public import Instance.Analysis.Section_2_2.Part2
public import Theorem.Nat.Eq0Add
public import Theorem.Nat.Eq_Add
public import Theorem.Nat.EqAdd1
public import Theorem.Nat.EqAdd2
public import Theorem.Nat.Eq_Add0
public import Theorem.Nat.AddEqAdd
public import Theorem.Nat.EqAddAdd
public import Theorem.Nat.Eq.of.Add
public import Theorem.Nat.IsPos.is.Ne_0
public import Theorem.Nat.IsPosAdd.of.IsPos
public import Theorem.Nat.Add.of.IsPos
public import Theorem.Nat.Eq_0.Eq_0.of.EqAdd_0
public import Theorem.Nat.Le.is.Any_Eq_Add
public import Theorem.Nat.Lt.is.Any_Eq_AddAndNe
public import Theorem.Nat.GeIffLe
public import Theorem.Nat.GtIffLt
public import Theorem.Nat.Le.of.Lt_Nat_le_of_lt
public import Theorem.Nat.Le.is.LtOrEq
public import Theorem.Nat.Le_Nat_le_refl
public import Theorem.Nat.Le.of.Le.Le_Nat_le_trans
public import Theorem.Nat.Ge.is.Add.ge.Add
public import Theorem.Nat.Le.is.Add.le.Add
public import Theorem.Nat.IffLeLeAdd
public import Theorem.Nat.Ne_Nat_ne_of_lt
public import Theorem.Nat.Ne_Nat_ne_of_gt
public import Theorem.Nat.False_Nat_not_lt_of_gt
public import Theorem.Nat.False.of.Lt
public import Theorem.Nat.Lt.of.Lt.Le_Nat_lt_of_le_of_lt

@[expose] public section


namespace Chapter2

@[simp] abbrev Nat.zero_add (m : Nat) : 0 + m = m := @_root_.Nat.Eq0Add m

abbrev Nat.succ_add (n m : Nat) : n++ + m = (n + m)++ := @_root_.Nat.Eq_Add n m

abbrev Nat.one_add (m : Nat) : 1 + m = m++ := @_root_.Nat.EqAdd1 m

abbrev Nat.two_add (m : Nat) : 2 + m = (m++)++ := @_root_.Nat.EqAdd2 m

abbrev Nat.add_zero (n : Nat) : n + 0 = n := @_root_.Nat.Eq_Add0 n

abbrev Nat.add_succ (n m : Nat) : n + (m++) = (n + m)++ := @_root_.Nat.AddEqAdd n m

abbrev Nat.add_comm (n m : Nat) : n + m = m + n := @_root_.Nat.EqAddAdd n m

abbrev Nat.add_left_cancel {a b c : Nat} (habc : a + b = a + c) : b = c := _root_.Nat.Eq.of.Add habc

abbrev Nat.isPos_iff (n : Nat) : n.IsPos ↔ n ≠ 0 := @_root_.Nat.IsPos.is.Ne_0 n

abbrev Nat.add_pos_left {a : Nat} (b : Nat) (ha : a.IsPos) : (a + b).IsPos := _root_.Nat.IsPosAdd.of.IsPos ha

abbrev Nat.add_pos_right {a : Nat} (b : Nat) (ha : a.IsPos) : (b + a).IsPos := _root_.Nat.Add.of.IsPos ha

abbrev Nat.add_eq_zero (a b : Nat) (hab : a + b = 0) : a = 0 ∧ b = 0 := _root_.Nat.Eq_0.Eq_0.of.EqAdd_0 hab

abbrev Nat.le_iff (n m : Nat) : n ≤ m ↔ ∃ a : Nat, m = n + a := @_root_.Nat.Le.is.Any_Eq_Add n m

abbrev Nat.lt_iff (n m : Nat) : n < m ↔ (∃ a : Nat, m = n + a) ∧ n ≠ m := @_root_.Nat.Lt.is.Any_Eq_AddAndNe n m

@[symm] abbrev Nat.ge_iff_le (n m : Nat) : n ≥ m ↔ m ≤ n := @_root_.Nat.GeIffLe n m

@[symm] abbrev Nat.gt_iff_lt (n m : Nat) : n > m ↔ m < n := @_root_.Nat.GtIffLt n m

abbrev Nat.le_of_lt {n m : Nat} (hnm : n < m) : n ≤ m := _root_.Nat.Le.of.Lt_Nat_le_of_lt hnm

abbrev Nat.le_iff_lt_or_eq (n m : Nat) : n ≤ m ↔ n < m ∨ n = m := @_root_.Nat.Le.is.LtOrEq n m

@[refl] abbrev Nat.le_refl (a : Nat) : a ≤ a := @_root_.Nat.Le_Nat_le_refl a

abbrev Nat.le_trans {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := _root_.Nat.Le.of.Le.Le_Nat_le_trans hab hbc

abbrev Nat.add_ge_add_left (a b c : Nat) : a ≥ b ↔ c + a ≥ c + b := @_root_.Nat.Ge.is.Add.ge.Add a b c

abbrev Nat.add_le_add_right (a b c : Nat) : a ≤ b ↔ a + c ≤ b + c := @_root_.Nat.Le.is.Add.le.Add a b c

abbrev Nat.add_le_add_left (a b c : Nat) : a ≤ b ↔ c + a ≤ c + b := @_root_.Nat.IffLeLeAdd a b c

abbrev Nat.ne_of_lt (a b : Nat) : a < b → a ≠ b := @_root_.Nat.Ne_Nat_ne_of_lt a b

abbrev Nat.ne_of_gt (a b : Nat) : a > b → a ≠ b := @_root_.Nat.Ne_Nat_ne_of_gt a b

abbrev Nat.not_lt_of_gt (a b : Nat) : a < b ∧ a > b → False := @_root_.Nat.False_Nat_not_lt_of_gt a b

abbrev Nat.not_lt_self {a : Nat} (h : a < a) : False := _root_.Nat.False.of.Lt h

abbrev Nat.lt_of_le_of_lt {a b c : Nat} (hab : a ≤ b) (hbc : b < c) : a < c :=
  _root_.Nat.Lt.of.Lt.Le_Nat_lt_of_le_of_lt hab hbc

end Chapter2
