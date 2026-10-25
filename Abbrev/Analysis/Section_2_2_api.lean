import Instance.Analysis.Section_2_2.Part2
import Lemma.Nat.Eq0Add
import Lemma.Nat.Eq_Add
import Lemma.Nat.EqAdd1
import Lemma.Nat.EqAdd2
import Lemma.Nat.Eq_Add0
import Lemma.Nat.AddEqAdd
import Lemma.Nat.EqAddAdd
import Lemma.Nat.Eq.of.Add
import Lemma.Nat.IsPos.is.Ne_0
import Lemma.Nat.IsPosAdd.of.IsPos
import Lemma.Nat.Add.of.IsPos
import Lemma.Nat.Eq_0.Eq_0.of.EqAdd_0
import Lemma.Nat.Le.is.Any_Eq_Add
import Lemma.Nat.Lt.is.Any_Eq_AddAndNe
import Lemma.Nat.GeIffLe
import Lemma.Nat.GtIffLt
import Lemma.Nat.Le.of.Lt_Nat_le_of_lt
import Lemma.Nat.Le.is.LtOrEq
import Lemma.Nat.Le_Nat_le_refl
import Lemma.Nat.Le.of.Le.Le_Nat_le_trans
import Lemma.Nat.Ge.is.Add.ge.Add
import Lemma.Nat.Le.is.Add.le.Add
import Lemma.Nat.IffLeLeAdd
import Lemma.Nat.Ne_Nat_ne_of_lt
import Lemma.Nat.Ne_Nat_ne_of_gt
import Lemma.Nat.False_Nat_not_lt_of_gt
import Lemma.Nat.False.of.Lt
import Lemma.Nat.Lt.of.Lt.Le_Nat_lt_of_le_of_lt


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
