import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.BurnsidePaqbReduction
open BurnsidePaqb


/--
[mem_conjClass_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqbReduction.lean)
-/
@[path]
private lemma mem_conjClass_iff_eq
  [Group G] [Fintype G]
  {g h : G} :
-- imply
  h ∈ conjClass g ↔ IsConj h g := by
-- proof
  apply BurnsidePaqb.mem_conjClass_iff

/--
[conjClass_card_mul_stabilizer_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqbReduction.lean)
-/
@[path]
private lemma conjClass_card_mul_stabilizer_card_eq
  [Group G] [Fintype G]
  {g : G} :
-- imply
  (conjClass g).card * Fintype.card (MulAction.stabilizer (ConjAct G) g) =
    Fintype.card G := by
-- proof
  apply BurnsidePaqb.conjClass_card_mul_stabilizer_card g

/--
[centralizer_card_eq_stabilizer_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqbReduction.lean)
-/
@[path]
private lemma centralizer_card_eq_stabilizer_card_eq
  [Group G] [Fintype G]
  {g : G} :
-- imply
  Fintype.card (Subgroup.centralizer {g}) =
    Fintype.card (MulAction.stabilizer (ConjAct G) g) := by
-- proof
  apply BurnsidePaqb.centralizer_card_eq_stabilizer_card g

/--
[conjClass_card_mul_centralizer_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqbReduction.lean)
-/
@[path]
private lemma conjClass_card_mul_centralizer_card_eq
  [Group G] [Fintype G]
  {g : G} :
-- imply
  (conjClass g).card * Fintype.card (Subgroup.centralizer {g}) = Fintype.card G := by
-- proof
  apply BurnsidePaqb.conjClass_card_mul_centralizer_card g

/--
[conj_mem_conjClass](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqbReduction.lean)
-/
@[path]
private lemma conj_mem_conjClass_eq
  [Group G] [Fintype G]
  {g h x : G}
-- given
  (hx : x ∈ conjClass g) :
-- imply
  h * x * h⁻¹ ∈ conjClass g := by
-- proof
  apply BurnsidePaqb.conj_mem_conjClass g h x hx

/--
[exists_ne_one_class_prime_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqbReduction.lean)
-/
@[path]
private lemma exists_ne_one_class_prime_pow_eq
  [Group G] [Fintype G]
  {p q a b : ℕ}
-- given
  (hp : p.Prime)
  (hq : q.Prime)
  (hcard : Fintype.card G = p ^ a * q ^ b)
  (hb : 1 ≤ b) :
-- imply
  ∃ g : G, g ≠ 1 ∧ ∃ k ≤ a, (conjClass g).card = p ^ k := by
-- proof
  apply BurnsidePaqb.exists_ne_one_class_prime_pow hp hq hcard hb


-- created on 2026-10-20
