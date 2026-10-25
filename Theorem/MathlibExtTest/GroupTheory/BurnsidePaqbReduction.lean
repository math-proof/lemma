/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/BurnsidePaqbReduction.lean -/


import Theorem.GroupTheory.BurnsidePaqbReduction.Part2
import Mathlib.Data.ZMod.Basic
open BurnsidePaqb

/-!
# Compile-time tests for the `p^a * q^b` conjugacy-class reduction

Authors: Muse Spark 1.3
-/


-- Membership characterization of the conjugacy-class finset.
example {G : Type*} [Group G] [Fintype G] {g h : G} :
    h ∈ conjClass g ↔ IsConj h g :=
  mem_conjClass_iff

-- Orbit-stabilizer and centralizer cardinality facts specialize correctly.

open Classical in
example {G : Type*} [Group G] [Fintype G] (g : G) :
    (conjClass g).card * Fintype.card (MulAction.stabilizer (ConjAct G) g) =
      Fintype.card G :=
  conjClass_card_mul_stabilizer_card g

open Classical in
example {G : Type*} [Group G] [Fintype G] (g : G) :
    (conjClass g).card * Fintype.card (Subgroup.centralizer {g}) =
      Fintype.card G :=
  conjClass_card_mul_centralizer_card g

-- The centralizer–stabilizer equivalence has the expected type.
example {G : Type*} [Group G] [Fintype G] (g : G) :
    Subgroup.centralizer {g} ≃ MulAction.stabilizer (ConjAct G) g :=
  centralizerEquivStabilizer g

-- Conjugation closure specializes correctly.
example {G : Type*} [Group G] [Fintype G] (g h x : G) (hx : x ∈ conjClass g) :
    h * x * h⁻¹ ∈ conjClass g :=
  conj_mem_conjClass g h x hx

-- Boundary regime `p = q`: a group of order `2 ^ 1 * 2 ^ 1`.
example : ∃ g : Multiplicative (ZMod 4), g ≠ 1 ∧ ∃ k ≤ 1,
    (conjClass g).card = 2 ^ k :=
  exists_ne_one_class_prime_pow (p := 2) (q := 2) (a := 1) (b := 1)
    (by decide) (by decide) (by decide) (by norm_num)

-- Boundary regime with zero exponent `a = 0`: a group of order `2 ^ 0 * 3 ^ 1`.
example : ∃ g : Multiplicative (ZMod 3), g ≠ 1 ∧ ∃ k ≤ 0,
    (conjClass g).card = 2 ^ k :=
  exists_ne_one_class_prime_pow (p := 2) (q := 3) (a := 0) (b := 1)
    (by decide) (by decide) (by decide) (by norm_num)

