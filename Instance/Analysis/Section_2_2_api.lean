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
import Abbrev.Analysis.Section_2_2_api


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
