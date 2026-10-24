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

/-- The concrete `n²`-dimensional Taft algebra over a field `k` (with parameter `q`), realized
as functions `Fin n × Fin n → k` giving coefficients in the basis `{g^a x^b}`. -/
@[ext]
structure TaftAlgebraType (n : ℕ) (q : k) (k : Type*) [Field k] where
  coeff : Fin n × Fin n → k

variable {k : Type*} [Field k] {n : ℕ} [NeZero n] {q : k}

set_option linter.unusedSectionVars false
namespace TaftAlgebraType

/-- The zero element of `TaftAlgebraType` has all coefficients equal to zero. -/
noncomputable instance : Zero (TaftAlgebraType n q k) := ⟨⟨0⟩⟩
/-- Pointwise addition of coefficient vectors in `TaftAlgebraType`. -/
noncomputable instance : Add (TaftAlgebraType n q k) := ⟨fun a b => ⟨a.coeff + b.coeff⟩⟩
/-- Pointwise negation of coefficient vectors in `TaftAlgebraType`. -/
noncomputable instance : Neg (TaftAlgebraType n q k) := ⟨fun a => ⟨-a.coeff⟩⟩
/-- Pointwise subtraction of coefficient vectors in `TaftAlgebraType`. -/
noncomputable instance : Sub (TaftAlgebraType n q k) := ⟨fun a b => ⟨a.coeff - b.coeff⟩⟩
/-- Pointwise scalar multiplication by `k` on `TaftAlgebraType`. -/
noncomputable instance instSMul : SMul k (TaftAlgebraType n q k) := ⟨fun r a => ⟨r • a.coeff⟩⟩

/-- Coefficient of the zero element. -/
@[simp] lemma coeff_zero' (i : Fin n × Fin n) : (0 : TaftAlgebraType n q k).coeff i = 0 := rfl
/-- Coefficients distribute over addition. -/
@[simp] lemma coeff_add (a b : TaftAlgebraType n q k) (i : Fin n × Fin n) :
    (a + b).coeff i = a.coeff i + b.coeff i := rfl
/-- Coefficients commute with negation. -/
@[simp] lemma coeff_neg (a : TaftAlgebraType n q k) (i : Fin n × Fin n) :
    (-a).coeff i = -a.coeff i := rfl
/-- Coefficients distribute over subtraction. -/
@[simp] lemma coeff_sub (a b : TaftAlgebraType n q k) (i : Fin n × Fin n) :
    (a - b).coeff i = a.coeff i - b.coeff i := rfl
/-- Coefficients of a scalar multiple are scaled coefficients. -/
@[simp] lemma coeff_smul (r : k) (a : TaftAlgebraType n q k) (i : Fin n × Fin n) :
    (r • a).coeff i = r * a.coeff i := rfl

/-- Structure constants for the Taft-algebra multiplication on the basis `{g^a x^b}`. The
product of `g^{i_1} x^{i_2}` and `g^{c_1} x^{c_2}` is the basis element `g^{(i_1+c_1) mod n}
x^{i_2+c_2}` with scalar coefficient `q^{n^2 - i_2 c_1}` when `i_2+c_2 < n`, and zero otherwise. -/
noncomputable def basisMul (q : k) (ij cd : Fin n × Fin n) : Fin n × Fin n → k := fun (e, f) =>
  if ij.2.val + cd.2.val < n
    ∧ e.val = (ij.1.val + cd.1.val) % n
    ∧ f.val = ij.2.val + cd.2.val
  then q ^ (n * n - ij.2.val * cd.1.val)
  else 0

/-- Multiplication on the Taft algebra: convolution against the basis structure constants. -/
noncomputable instance : Mul (TaftAlgebraType n q k) where
  mul a b := ⟨fun m => ∑ ij : Fin n × Fin n, ∑ cd : Fin n × Fin n,
    a.coeff ij * b.coeff cd * basisMul q ij cd m⟩

/-- The "origin" `(0, 0)` index, corresponding to the basis element `g^0 x^0 = 1`. -/
def zp : Fin n × Fin n := (⟨0, NeZero.pos n⟩, ⟨0, NeZero.pos n⟩)

/-- The unit element `1` of `TaftAlgebraType`: the indicator function of the origin index. -/
noncomputable instance : One (TaftAlgebraType n q k) where
  one := ⟨fun ij => if ij = zp then 1 else 0⟩

/-- The natural-number cast in `TaftAlgebraType` lives entirely at the origin index. -/
noncomputable instance : NatCast (TaftAlgebraType n q k) where
  natCast c := ⟨fun ij => if ij = zp then (c : k) else 0⟩

/-- The integer cast in `TaftAlgebraType` lives entirely at the origin index. -/
noncomputable instance : IntCast (TaftAlgebraType n q k) where
  intCast c := ⟨fun ij => if ij = zp then (c : k) else 0⟩

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
private lemma one_mul' (a : TaftAlgebraType n q k) : 1 * a = a := by
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
private lemma mul_one' (a : TaftAlgebraType n q k) : a * 1 = a := by
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
private lemma mul_assoc' (a b c : TaftAlgebraType n q k) : a * b * c = a * (b * c) := by
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
private lemma left_distrib' (a b c : TaftAlgebraType n q k) : a * (b + c) = a * b + a * c := by
  ext m; simp only [coeff_mul, coeff_add]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

/-- Right distributivity of multiplication over addition. -/
private lemma right_distrib' (a b c : TaftAlgebraType n q k) : (a + b) * c = a * c + b * c := by
  ext m; simp only [coeff_mul, coeff_add]
  simp_rw [add_mul, Finset.sum_add_distrib]

/-- The Taft algebra is an additive abelian group under pointwise operations on coefficients. -/
noncomputable instance : AddCommGroup (TaftAlgebraType n q k) where
  add_assoc a b c := by ext i; simp [add_assoc]
  zero_add a := by ext i; simp
  add_zero a := by ext i; simp
  add_comm a b := by ext i; simp [add_comm]
  neg_add_cancel a := by ext i; simp
  sub_eq_add_neg a b := by ext i; simp [sub_eq_add_neg]
  nsmul := fun c a => ⟨fun i => c • a.coeff i⟩
  nsmul_zero a := by ext i; simp
  nsmul_succ c a := by ext i; simp [add_mul, add_comm]
  zsmul := fun c a => ⟨fun i => c • a.coeff i⟩
  zsmul_zero' a := by ext i; simp
  zsmul_succ' c a := by ext i; simp [add_mul, add_comm]
  zsmul_neg' c a := by ext i; simp [Int.negSucc_eq]; ring

/-- The Taft algebra is a ring under the convolution multiplication and additive group
structure. -/
noncomputable instance : Ring (TaftAlgebraType n q k) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  zero_mul a := by ext m; simp [zero_mul, Finset.sum_const_zero]
  mul_zero a := by ext m; simp [mul_zero, Finset.sum_const_zero]
  natCast_zero := by ext m; simp
  natCast_succ c := by ext m; simp; split <;> simp
  intCast_ofNat c := by ext m; simp
  intCast_negSucc c := by ext m; simp [Int.negSucc_eq]; split <;> simp

/-- `k`-module structure on the Taft algebra via pointwise scalar multiplication of
coefficients. -/
noncomputable instance : Module k (TaftAlgebraType n q k) where
  one_smul a := by ext i; simp
  mul_smul r s a := by ext i; simp [mul_assoc]
  smul_zero r := by ext i; simp
  smul_add r a b := by ext i; simp [mul_add]
  add_smul r s a := by ext i; simp [add_mul]
  zero_smul a := by ext i; simp

/-- `k`-algebra structure on the Taft algebra, derived from the module and ring structures via
`Algebra.ofModule`. -/
noncomputable instance : Algebra k (TaftAlgebraType n q k) :=
  Algebra.ofModule
    (fun r x y => by
      ext m; simp only [coeff_smul, coeff_mul]
      rw [Finset.mul_sum]; congr 1; ext i
      rw [Finset.mul_sum]; congr 1; ext j; ring)
    (fun r x y => by
      ext m; simp only [coeff_smul, coeff_mul]
      rw [Finset.mul_sum]; congr 1; ext i
      rw [Finset.mul_sum]; congr 1; ext j; ring)

/-- `k`-linear equivalence between `TaftAlgebraType n q k` and `Fin n × Fin n → k`. -/
noncomputable def toFunEquiv : TaftAlgebraType n q k ≃ₗ[k] (Fin n × Fin n → k) where
  toFun a := a.coeff
  invFun f := ⟨f⟩
  map_add' a b := rfl
  map_smul' r a := by ext i; simp [Pi.smul_apply, smul_eq_mul]
  left_inv a := rfl
  right_inv f := rfl

/-- `Module.finrank k (TaftAlgebraType n q k) = n * n`. -/
lemma finrank_eq : Module.finrank k (TaftAlgebraType n q k) = n * n := by
  rw [LinearEquiv.finrank_eq toFunEquiv, Module.finrank_pi_fintype, Module.finrank_self,
      Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_prod]
  simp [Fintype.card_fin]

/-- The basis element `e ij ∈ TaftAlgebraType n q k` corresponding to the basis vector `g^{i_1}
x^{i_2}`. -/
def e (ij : Fin n × Fin n) : TaftAlgebraType n q k where
  coeff := fun p => if ij = p then 1 else 0

/-- The generator `g` of the Taft algebra, equal to the basis element `e (1, 0)`. -/
def gen_g (hn2 : n ≥ 2) : TaftAlgebraType n q k :=
  e (⟨1, by omega⟩, ⟨0, NeZero.pos n⟩)

/-- The generator `x` of the Taft algebra, equal to the basis element `e (0, 1)`. -/
def gen_x (hn2 : n ≥ 2) : TaftAlgebraType n q k :=
  e (⟨0, NeZero.pos n⟩, ⟨1, by omega⟩)

/-- The coefficient of `e ij` at index `p` is `1` iff `ij = p`, else `0`. -/
@[simp] lemma coeff_e (ij p : Fin n × Fin n) :
    (e ij : TaftAlgebraType n q k).coeff p = if ij = p then 1 else 0 := rfl
