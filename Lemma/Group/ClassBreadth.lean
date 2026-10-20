import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.ClassBreadth
open ClassBreadth


/--
[card_carrier_dvd_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean)
-/
@[path]
private lemma card_carrier_dvd_card_eq
  [Group G] [Finite G]
  {g : G} :
-- imply
  Nat.card (ConjClasses.mk g).carrier ∣ Nat.card G := by
-- proof
  apply ClassBreadth.card_carrier_dvd_card g

/--
[exists_card_carrier_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean)
-/
@[path]
private lemma exists_card_carrier_eq_pow_eq
  [Group G] [Finite G]
  {p : ℕ} [Fact p.Prime]
  {g : G}
-- given
  (hG : IsPGroup p G) :
-- imply
  ∃ k : ℕ, Nat.card (ConjClasses.mk g).carrier = p ^ k := by
-- proof
  apply ClassBreadth.exists_card_carrier_eq_pow p hG g

/--
[elementBreadth_eq_of_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean)
-/
@[path]
private lemma elementBreadth_eq_of_card_eq_eq
  [Group G] [Finite G]
  {p k : ℕ}
  {g : G}
-- given
  (hp : p.Prime)
  (h : Nat.card (ConjClasses.mk g).carrier = p ^ k) :
-- imply
  elementBreadth p g = k := by
-- proof
  apply ClassBreadth.elementBreadth_eq_of_card_eq hp g h

/--
[pow_elementBreadth_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean)
-/
@[path]
private lemma pow_elementBreadth_eq_card_eq
  [Group G] [Finite G]
  {p : ℕ} [Fact p.Prime]
  {g : G}
-- given
  (hG : IsPGroup p G) :
-- imply
  p ^ elementBreadth p g = Nat.card (ConjClasses.mk g).carrier := by
-- proof
  apply ClassBreadth.pow_elementBreadth_eq_card p hG g

/--
[carrier_mk_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean)
-/
@[path]
private lemma carrier_mk_one_eq
  [Group G] :
-- imply
  (ConjClasses.mk (1 : G)).carrier = {1} := by
-- proof
  apply ClassBreadth.carrier_mk_one

/--
[elementBreadth_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean)
-/
@[path]
private lemma elementBreadth_one_eq
  [Group G] [Finite G]
  {p : ℕ} :
-- imply
  elementBreadth p (1 : G) = 0 := by
-- proof
  apply ClassBreadth.elementBreadth_one p

/--
[elementBreadth_le_breadth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean)
-/
@[path]
private lemma elementBreadth_le_breadth_eq
  [Group G] [Fintype G]
  {p : ℕ}
  {g : G} :
-- imply
  elementBreadth p g ≤ breadth p G := by
-- proof
  apply ClassBreadth.elementBreadth_le_breadth p g

/--
[exists_breadth_eq_elementBreadth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean)
-/
@[path]
private lemma exists_breadth_eq_elementBreadth_eq
  [Group G] [Fintype G] [Nonempty G]
  {p : ℕ} :
-- imply
  ∃ g : G, breadth p G = elementBreadth p g := by
-- proof
  apply ClassBreadth.exists_breadth_eq_elementBreadth p


-- created on 2026-10-20
