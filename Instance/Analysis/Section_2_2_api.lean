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
public import Abbrev.Analysis.Section_2_2_api
@[expose] public section

namespace Chapter2

/-- (Not from textbook) `Nat` can be given the structure of a commutative additive monoid. -/
instance Nat.addCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- (Not from textbook) `Nat` has the structure of a linear ordering. -/
instance Nat.instLinearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans a b c hab hbc := ge_trans hbc hab
  lt_iff_le_not_ge a b := by
    constructor
    . intro h; refine ⟨ le_of_lt h, ?_ ⟩
      by_contra h'
      exact not_lt_self (lt_of_le_of_lt h' h)
    rintro ⟨ h1, h2 ⟩
    rw [lt_iff, ←le_iff]; refine ⟨ h1, ?_ ⟩
    by_contra h
    subst h
    contradiction
  le_antisymm a b hab hba := ge_antisymm hba hab
  le_total a b := by
    obtain h | rfl | h := trichotomous a b
    . left; exact le_of_lt h
    . simp [ge_refl]
    . right; exact le_of_lt h
  toDecidableLE := decidableRel

instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left a b hab c := (Nat.add_le_add_right a b c).mp hab

end Chapter2
