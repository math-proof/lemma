/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.Prod
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Instance.v1.Atlas.TensorCategories.code.TaftConcrete.Part3
variable {k : Type*} [Field k] {n : ℕ} [NeZero n] {q : k}

set_option linter.unusedSectionVars false


namespace TaftAlgebraType

/-- Definitional unfolding of the product coefficient as a double sum against `basisMul`. -/
@[simp] lemma coeff_mul (a b : TaftAlgebraType n q k) (m : Fin n × Fin n) :
    (a * b).coeff m = ∑ ij : Fin n × Fin n, ∑ cd : Fin n × Fin n,
      a.coeff ij * b.coeff cd * basisMul q ij cd m := rfl

/-- Definitional unfolding of the coefficient of `1`. -/
@[simp] lemma coeff_one (m : Fin n × Fin n) :
    (1 : TaftAlgebraType n q k).coeff m = if m = zp then 1 else 0 := rfl

/-- Definitional unfolding of the coefficient of a natural-number cast. -/
@[simp] lemma coeff_natCast (c : ℕ) (m : Fin n × Fin n) :
    (c : TaftAlgebraType n q k).coeff m = if m = zp then (c : k) else 0 := rfl

/-- Definitional unfolding of the coefficient of an integer cast. -/
@[simp] lemma coeff_intCast (c : ℤ) (m : Fin n × Fin n) :
    (c : TaftAlgebraType n q k).coeff m = if m = zp then (c : k) else 0 := rfl

/-- If `basisMul q ij cd ef ≠ 0`, then the index constraints in the `if` of `basisMul` must
hold: `i_2 + c_2 < n` and `ef = ((i_1+c_1) mod n, i_2+c_2)`. -/
lemma basisMul_ne_zero_imp {q : k} {ij cd ef : Fin n × Fin n}
    (h : basisMul q ij cd ef ≠ 0) :
    ij.2.val + cd.2.val < n ∧ ef.1.val = (ij.1.val + cd.1.val) % n
      ∧ ef.2.val = ij.2.val + cd.2.val := by
  simp only [basisMul] at h; by_contra h'; simp [if_neg h'] at h

/-- If `i_2 + c_2 ≥ n`, then `basisMul q ij cd b` vanishes (we hit the relation `x^n = 0`). -/
lemma basisMul_zero_of_ge (q : k) (ij cd b : Fin n × Fin n)
    (h : ¬(ij.2.val + cd.2.val < n)) :
    basisMul q ij cd b = 0 := by
  simp only [basisMul]; apply if_neg; push Not; intro; exact absurd ‹_› h

/-- Triple-product vanishing: if `i_2 + c_2 + l_2 ≥ n` then the product
`basisMul q ij cd p * basisMul q p l m` vanishes for every `p`. -/
lemma basisMul_prod_zero_of_ge (q : k) (ij cd p l m : Fin n × Fin n)
    (h : ¬(ij.2.val + cd.2.val + l.2.val < n)) :
    basisMul q ij cd p * basisMul q p l m = 0 := by
  by_cases h1 : ij.2.val + cd.2.val < n
  · by_cases h2 : basisMul q ij cd p = 0
    · simp [h2]
    · have hp := basisMul_ne_zero_imp h2
      have : ¬(p.2.val + l.2.val < n) := by omega
      simp [basisMul_zero_of_ge q p l m this]
  · simp [basisMul_zero_of_ge q ij cd p h1]

/-- If `q^n = 1`, then `q^(n²) = 1`. -/
lemma q_pow_nsq (hq : q ^ n = 1) : q ^ (n * n) = 1 := by
  rw [pow_mul, hq, one_pow]

/-- Left identity for `basisMul`: `basisMul q (0,0) cd ef = 1` if `cd = ef` and `0` otherwise. -/
lemma basisMul_id_left (hq : q ^ n = 1) (cd ef : Fin n × Fin n) :
    basisMul q zp cd ef = if cd = ef then 1 else 0 := by
  simp only [basisMul, zp, zero_mul, Nat.sub_zero, zero_add]
  rw [Nat.mod_eq_of_lt cd.1.isLt]; simp only [cd.2.isLt, true_and]
  by_cases h : cd = ef
  · subst h; simp [q_pow_nsq hq]
  · simp only [h, ite_false]
    apply if_neg; push Not
    intro h1 h2
    exact h (Prod.ext (Fin.ext h1.symm) (Fin.ext h2.symm))

/-- Right identity for `basisMul`: `basisMul q ij (0,0) ef = 1` if `ij = ef` and `0` otherwise. -/
lemma basisMul_id_right (hq : q ^ n = 1) (ij ef : Fin n × Fin n) :
    basisMul q ij zp ef = if ij = ef then 1 else 0 := by
  simp only [basisMul, zp, Nat.add_zero, mul_zero, Nat.sub_zero]
  rw [Nat.mod_eq_of_lt ij.1.isLt]; simp only [ij.2.isLt, true_and]
  by_cases h : ij = ef
  · subst h; simp [q_pow_nsq hq]
  · simp only [h, ite_false]
    apply if_neg; push Not
    intro h1 h2
    exact h (Prod.ext (Fin.ext h1.symm) (Fin.ext h2.symm))

/-- When `q^n = 1`, the power `q^(n² - x)` equals `(q^x)⁻¹` for any `x ≤ n²`. -/
lemma pow_nn_sub_eq_inv (hq : q ^ n = 1) (x : ℕ) (hx : x ≤ n * n) :
    q ^ (n * n - x) = (q ^ x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_add, Nat.sub_add_cancel hx, pow_mul, hq, one_pow])

/-- When `q^n = 1`, the power `q^(b * m)` depends only on `m mod n` in the exponent. -/
lemma pow_mul_mod_eq (hq : q ^ n = 1) (b m : ℕ) : q ^ (b * m) = q ^ (b * (m % n)) := by
  conv_lhs => rw [← Nat.div_add_mod m n]
  rw [show b * (n * (m / n) + m % n) = n * (b * (m / n)) + b * (m % n) from by ring]
  rw [pow_add, pow_mul, hq, one_pow, one_mul]

/-- Identity of `q`-power expressions arising in the proof of associativity for the Taft
multiplication; reduces both sides to a common normal form using `q^n = 1`. -/
lemma q_pow_assoc_identity (hq : q ^ n = 1) (b c d e : ℕ)
    (hb : b < n) (hc : c < n) (he : e < n) (hbd : b + d < n) :
    q ^ (n * n - b * c) * q ^ (n * n - (b + d) * e) =
    q ^ (n * n - d * e) * q ^ (n * n - b * ((c + e) % n)) := by
  have hbc_le : b * c ≤ n * n := by nlinarith
  have hbde_le : (b + d) * e ≤ n * n := by nlinarith
  have hde_le : d * e ≤ n * n := by nlinarith
  have hbce_le : b * ((c + e) % n) ≤ n * n := by
    have : (c + e) % n < n := Nat.mod_lt _ (by omega)
    nlinarith
  rw [pow_nn_sub_eq_inv hq _ hbc_le, pow_nn_sub_eq_inv hq _ hbde_le,
      pow_nn_sub_eq_inv hq _ hde_le, pow_nn_sub_eq_inv hq _ hbce_le,
      ← mul_inv, ← mul_inv, ← pow_add, ← pow_add]
  congr 1
  have h1 : b * c + (b + d) * e = b * (c + e) + d * e := by ring
  rw [h1, pow_add, pow_mul_mod_eq hq b (c + e), ← pow_add, add_comm]

variable [Fact (q ^ n = 1)]

/-- Extract `q^n = 1` from the typeclass assumption `Fact (q^n = 1)`. -/
lemma hq : q ^ n = 1 := Fact.out

/-- Left multiplicative identity: `1 * a = a` in the Taft algebra. -/
lemma one_mul' (a : TaftAlgebraType n q k) : 1 * a = a := by
  ext m
  show ∑ ij : Fin n × Fin n, ∑ cd : Fin n × Fin n,
    (if ij = zp then 1 else 0) * a.coeff cd * basisMul q ij cd m = a.coeff m
  have : ∀ ij : Fin n × Fin n,
    (∑ cd, (if ij = zp then 1 else 0) * a.coeff cd * basisMul q ij cd m) =
    if ij = zp then ∑ cd, a.coeff cd * basisMul q zp cd m else 0 := by
    intro ij; split_ifs with h <;> simp [h]
  simp_rw [this, Finset.sum_ite_eq' Finset.univ zp, if_pos (Finset.mem_univ _),
    basisMul_id_left hq, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq' Finset.univ m, if_pos (Finset.mem_univ _)]

/-- Right multiplicative identity: `a * 1 = a` in the Taft algebra. -/
lemma mul_one' (a : TaftAlgebraType n q k) : a * 1 = a := by
  ext m
  show ∑ ij : Fin n × Fin n, ∑ cd : Fin n × Fin n,
    a.coeff ij * (if cd = zp then 1 else 0) * basisMul q ij cd m = a.coeff m
  have inner : ∀ ij : Fin n × Fin n,
    (∑ cd, a.coeff ij * (if cd = zp then 1 else 0) * basisMul q ij cd m) =
    a.coeff ij * basisMul q ij zp m := by
    intro ij
    conv_lhs => arg 2; ext cd; rw [show a.coeff ij * (if cd = zp then 1 else 0) *
      basisMul q ij cd m = if cd = zp then a.coeff ij * basisMul q ij zp m else 0
      from by split_ifs with h <;> simp [h]]
    rw [Finset.sum_ite_eq' Finset.univ zp]; simp [Finset.mem_univ]
  simp_rw [inner, basisMul_id_right hq, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq' Finset.univ m, if_pos (Finset.mem_univ _)]

/-- Mod compatibility used in the associativity proof:
`((a + b) % n + c) % n = (a + (b + c) % n) % n`. -/
lemma mod_add_mod (a b c : ℕ) (_hn : 0 < n) :
    ((a + b) % n + c) % n = (a + (b + c) % n) % n := by
  rw [Nat.add_mod ((a + b) % n) c n]
  rw [Nat.mod_mod_of_dvd (a + b) ⟨1, by omega⟩]
  rw [← Nat.add_mod (a + b) c n]
  rw [Nat.add_mod a ((b+c) % n) n]
  rw [Nat.mod_mod_of_dvd (b + c) ⟨1, by omega⟩]
  rw [← Nat.add_mod a (b + c) n]
  congr 1; omega

set_option maxHeartbeats 800000 in
/-- Associativity of `basisMul` on basis indices: the two ways of bracketing the triple product
agree as sums over the intermediate index. -/
lemma basisMul_assoc_eq (ij cd l m : Fin n × Fin n) :
    ∑ p : Fin n × Fin n, basisMul q ij cd p * basisMul q p l m =
    ∑ r : Fin n × Fin n, basisMul q cd l r * basisMul q ij r m := by
  by_cases h_sum : ij.2.val + cd.2.val + l.2.val < n
  ·
    have h_bd : ij.2.val + cd.2.val < n := by omega
    have h_df : cd.2.val + l.2.val < n := by omega

    have lhs_single : ∀ p : Fin n × Fin n, basisMul q ij cd p * basisMul q p l m ≠ 0 →
        p = (⟨(ij.1.val + cd.1.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩,
             ⟨ij.2.val + cd.2.val, h_bd⟩) := by
      intro p hp
      have h1 : basisMul q ij cd p ≠ 0 := left_ne_zero_of_mul hp
      have h1' := basisMul_ne_zero_imp h1
      exact Prod.ext (Fin.ext h1'.2.1) (Fin.ext h1'.2.2)
    have rhs_single : ∀ r : Fin n × Fin n, basisMul q cd l r * basisMul q ij r m ≠ 0 →
        r = (⟨(cd.1.val + l.1.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩,
             ⟨cd.2.val + l.2.val, h_df⟩) := by
      intro r hr
      have h1 : basisMul q cd l r ≠ 0 := left_ne_zero_of_mul hr
      have h1' := basisMul_ne_zero_imp h1
      exact Prod.ext (Fin.ext h1'.2.1) (Fin.ext h1'.2.2)
    set p₀ : Fin n × Fin n := (⟨(ij.1.val + cd.1.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩,
               ⟨ij.2.val + cd.2.val, h_bd⟩)
    set r₀ : Fin n × Fin n := (⟨(cd.1.val + l.1.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩,
               ⟨cd.2.val + l.2.val, h_df⟩)
    rw [Finset.sum_eq_single p₀, Finset.sum_eq_single r₀]
    ·
      simp only [basisMul, p₀, r₀]
      simp only [h_bd, h_df, true_and]
      simp only [show (ij.2.val + cd.2.val + l.2.val < n) = True from
        propext ⟨fun _ => trivial, fun _ => h_sum⟩]
      simp only [show (ij.2.val + (cd.2.val + l.2.val) < n) = True from
        propext ⟨fun _ => trivial, fun _ => by omega⟩]
      simp only [true_and, if_true]
      have hmod : ((ij.1.val + cd.1.val) % n + l.1.val) % n =
          (ij.1.val + (cd.1.val + l.1.val) % n) % n :=
        mod_add_mod ij.1.val cd.1.val l.1.val (NeZero.pos n)
      have hm2 : ij.2.val + cd.2.val + l.2.val = ij.2.val + (cd.2.val + l.2.val) := by omega
      rw [hmod, hm2]

      split_ifs with h
      ·
        exact q_pow_assoc_identity hq ij.2.val cd.1.val cd.2.val l.1.val
          ij.2.isLt cd.1.isLt l.1.isLt h_bd
      ·
        simp
    · intro r _ hr; by_contra h; exact hr (rhs_single r h)
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro p _ hp; by_contra h; exact hp (lhs_single p h)
    · intro h; exact absurd (Finset.mem_univ _) h
  ·
    have lhs : ∀ p, basisMul q ij cd p * basisMul q p l m = 0 :=
      fun p => basisMul_prod_zero_of_ge q ij cd p l m h_sum
    have rhs : ∀ r, basisMul q cd l r * basisMul q ij r m = 0 := by
      intro r
      by_cases h1 : cd.2.val + l.2.val < n
      · by_cases h2 : basisMul q cd l r = 0
        · simp [h2]
        · have hr := basisMul_ne_zero_imp h2
          have : ¬(ij.2.val + r.2.val < n) := by omega
          simp [basisMul_zero_of_ge q ij r m this]
      · simp [basisMul_zero_of_ge q cd l r h1]
    simp [lhs, rhs, Finset.sum_const_zero]

set_option maxHeartbeats 800000 in
/-- Associativity of multiplication in the Taft algebra, by lifting `basisMul_assoc_eq`. -/
lemma mul_assoc' (a b c : TaftAlgebraType n q k) : a * b * c = a * (b * c) := by
  ext m
  simp only [coeff_mul]

  conv_lhs =>
    arg 2; ext p; arg 2; ext l
    rw [Finset.sum_mul, Finset.sum_mul]
    arg 2; ext ij; rw [Finset.sum_mul, Finset.sum_mul]
    arg 2; ext cd
    rw [show a.coeff ij * b.coeff cd * basisMul q ij cd p * c.coeff l * basisMul q p l m =
        a.coeff ij * b.coeff cd * c.coeff l * (basisMul q ij cd p * basisMul q p l m) by ring]

  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext l; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext ij; arg 2; ext l; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext ij; rw [Finset.sum_comm]

  conv_lhs =>
    arg 2; ext ij; arg 2; ext cd; arg 2; ext l
    rw [← Finset.mul_sum]

  conv_rhs =>
    arg 2; ext ij; arg 2; ext r
    rw [show (a.coeff ij * ∑ cd, ∑ l, b.coeff cd * c.coeff l * basisMul q cd l r) *
          basisMul q ij r m =
        ∑ cd, ∑ l, a.coeff ij * b.coeff cd * c.coeff l *
          (basisMul q cd l r * basisMul q ij r m) by
      rw [Finset.mul_sum]; simp_rw [Finset.mul_sum, Finset.sum_mul]
      congr 1; ext cd; congr 1; ext l; ring]

  conv_rhs => arg 2; ext ij; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext ij; arg 2; ext cd; rw [Finset.sum_comm]

  conv_rhs =>
    arg 2; ext ij; arg 2; ext cd; arg 2; ext l
    rw [← Finset.mul_sum]

  congr 1; ext ij; congr 1; ext cd; congr 1; ext l; congr 1
  exact basisMul_assoc_eq ij cd l m

/-- Left distributivity of multiplication over addition. -/
lemma left_distrib' (a b c : TaftAlgebraType n q k) : a * (b + c) = a * b + a * c := by
  ext m; simp only [coeff_mul, coeff_add]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

/-- Right distributivity of multiplication over addition. -/
lemma right_distrib' (a b c : TaftAlgebraType n q k) : (a + b) * c = a * c + b * c := by
  ext m; simp only [coeff_mul, coeff_add]
  simp_rw [add_mul, Finset.sum_add_distrib]

end TaftAlgebraType
