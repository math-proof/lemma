/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean -/

import Mathlib.Data.Nat.Log
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.PGroup

/-!
# Breadth of elements and finite groups

The breadth of an element `g` is the exponent `br(g)` with
`p ^ br(g) = |g^G|`, recovered as the base-`p` logarithm of the
conjugacy-class size. The breadth of a finite group is the maximum
element breadth. Every conjugacy-class size in a finite `p`-group is a
power of `p`, so the logarithm recovers the exact exponent.
-/

namespace ClassBreadth

variable {G : Type*} [Group G]

/-- The breadth of an element: the base-`p` logarithm of its conjugacy-class
size. In a finite `p`-group this is the exact exponent `br(g)` with
`p ^ br(g) = |g^G|` (see `pow_elementBreadth_eq_card`). -/
noncomputable def elementBreadth [Finite G] (p : ℕ) (g : G) : ℕ :=
  Nat.log p (Nat.card (ConjClasses.mk g).carrier)

/-- The breadth of a finite group: the maximum element breadth. -/
noncomputable def breadth (p : ℕ) (G : Type*) [Group G] [Fintype G] : ℕ :=
  Finset.univ.sup (fun g : G ↦ elementBreadth p g)

/-- A conjugacy-class size divides the group order. -/
theorem card_carrier_dvd_card [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier ∣ Nat.card G := by
  let _ := Fintype.ofFinite G
  classical
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g
  rw [ConjAct.orbit_eq_carrier_conjClasses] at h
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact ⟨Fintype.card (MulAction.stabilizer (ConjAct G) g), h.symm⟩

/-- In a finite `p`-group, every conjugacy-class size is a power of `p`. -/
theorem exists_card_carrier_eq_pow (p : ℕ) [Finite G] [Fact p.Prime]
    (hG : IsPGroup p G) (g : G) :
    ∃ k : ℕ, Nat.card (ConjClasses.mk g).carrier = p ^ k := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  have hdvd : Nat.card (ConjClasses.mk g).carrier ∣ p ^ n := hn ▸ card_carrier_dvd_card g
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
  exact ⟨k, hk⟩

/-- The logarithm recovers the exact exponent when the class size is a power. -/
theorem elementBreadth_eq_of_card_eq [Finite G] {p k : ℕ} (hp : p.Prime) (g : G)
    (h : Nat.card (ConjClasses.mk g).carrier = p ^ k) :
    elementBreadth p g = k := by
  rw [elementBreadth, h, Nat.log_pow hp.one_lt]

/-- Characteristic property: `p ^ br(g)` is the conjugacy-class size. -/
theorem pow_elementBreadth_eq_card (p : ℕ) [Finite G] [Fact p.Prime]
    (hG : IsPGroup p G) (g : G) :
    p ^ elementBreadth p g = Nat.card (ConjClasses.mk g).carrier := by
  obtain ⟨k, hk⟩ := exists_card_carrier_eq_pow p hG g
  rw [elementBreadth_eq_of_card_eq Fact.out g hk, hk]

/-- The conjugacy class of `1` is the singleton `{1}`. -/
theorem carrier_mk_one : (ConjClasses.mk (1 : G)).carrier = {1} := by
  ext x
  simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]

/-- The breadth of the identity element is zero. -/
theorem elementBreadth_one [Finite G] (p : ℕ) : elementBreadth p (1 : G) = 0 := by
  rw [elementBreadth, carrier_mk_one, Nat.card_unique, Nat.log_one_right]

/-- Every element breadth is bounded by the group breadth. -/
theorem elementBreadth_le_breadth (p : ℕ) [Fintype G] (g : G) :
    elementBreadth p g ≤ breadth p G :=
  Finset.le_sup (Finset.mem_univ g)

/-- The group breadth is attained at some element. -/
theorem exists_breadth_eq_elementBreadth (p : ℕ) [Fintype G] [Nonempty G] :
    ∃ g : G, breadth p G = elementBreadth p g := by
  obtain ⟨g, -, hg⟩ := Finset.exists_mem_eq_sup Finset.univ
    Finset.univ_nonempty (fun g : G ↦ elementBreadth p g)
  exact ⟨g, hg⟩

end ClassBreadth
