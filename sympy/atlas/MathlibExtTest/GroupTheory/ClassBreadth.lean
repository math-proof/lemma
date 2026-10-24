/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/ClassBreadth.lean -/


import sympy.atlas.GroupTheory.ClassBreadth
import Lemma.Nat.CardCarrier.dvd.CardG
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.PGroup


/-!
# Examples for class breadth

Exercises the `ClassBreadth` API on the cyclic group of order three:
the identity has breadth zero, the characteristic `p ^ br(g) = |g^G|`
holds, and the group breadth is zero since every conjugacy class is a
singleton.
-/

open ClassBreadth

/-- The cyclic group of order three is a `3`-group. -/
example : IsPGroup 3 (Multiplicative (ZMod 3)) := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [IsPGroup.iff_card]
  exact ⟨1, by simp [Nat.card_eq_fintype_card, ZMod.card]⟩

/-- The identity element has breadth zero. -/
example : elementBreadth 3 (1 : Multiplicative (ZMod 3)) = 0 :=
  elementBreadth_one 3

/-- Every element of `C₃` has breadth zero: conjugacy classes are singletons. -/
example (g : Multiplicative (ZMod 3)) : elementBreadth 3 g = 0 := by
  have h : (ConjClasses.mk g).carrier = {g} := by
    ext x
    simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj,
      isConj_iff_eq]
  rw [elementBreadth, h, Nat.card_unique, Nat.log_one_right]

/-- The breadth of `C₃` is zero. -/
example : breadth 3 (Multiplicative (ZMod 3)) = 0 := by
  have hall : ∀ g : Multiplicative (ZMod 3), elementBreadth 3 g = 0 := by
    intro g
    have h : (ConjClasses.mk g).carrier = {g} := by
      ext x
      simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj,
        isConj_iff_eq]
    rw [elementBreadth, h, Nat.card_unique, Nat.log_one_right]
  rw [breadth]
  exact le_antisymm (Finset.sup_le fun g _ => le_of_eq (hall g)) zero_le

/-- Characteristic property on `C₃`: `3 ^ br(g)` is the class size. -/
example (g : Multiplicative (ZMod 3)) :
    3 ^ elementBreadth 3 g = Nat.card (ConjClasses.mk g).carrier := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hG : IsPGroup 3 (Multiplicative (ZMod 3)) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by simp [Nat.card_eq_fintype_card, ZMod.card]⟩
  exact pow_elementBreadth_eq_card 3 hG g

/-- The breadth bound and attainment on `C₃`. -/
example (g : Multiplicative (ZMod 3)) :
    elementBreadth 3 g ≤ breadth 3 (Multiplicative (ZMod 3)) :=
  elementBreadth_le_breadth 3 g

example : ∃ g : Multiplicative (ZMod 3),
    breadth 3 (Multiplicative (ZMod 3)) = elementBreadth 3 g :=
  exists_breadth_eq_elementBreadth 3
