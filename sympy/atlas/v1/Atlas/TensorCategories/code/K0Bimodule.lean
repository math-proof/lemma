/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.GrothendieckRing
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Group.Opposite

set_option maxHeartbeats 800000

open Finset FusionRing

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- The Grothendieck group `K₀(R)` of a fusion ring `R`, represented as integer-valued
coefficient vectors indexed by the basis `ι`. -/
@[ext]
structure K0Group (R : FusionRing ι) where
  coeff : ι → ℤ

namespace K0Group

variable {R : FusionRing ι}

/-- The zero element of `K₀(R)` is the all-zero coefficient vector. -/
instance : Zero (K0Group R) := ⟨⟨fun _ => 0⟩⟩
/-- Componentwise addition of elements of `K₀(R)`. -/
instance : Add (K0Group R) := ⟨fun a b => ⟨fun k => a.coeff k + b.coeff k⟩⟩
/-- Componentwise negation on `K₀(R)`. -/
instance : Neg (K0Group R) := ⟨fun a => ⟨fun k => -a.coeff k⟩⟩
/-- Componentwise subtraction on `K₀(R)`. -/
instance : Sub (K0Group R) := ⟨fun a b => ⟨fun k => a.coeff k - b.coeff k⟩⟩

/-- Natural-number scalar multiplication on `K₀(R)`, applied componentwise. -/
instance : SMul ℕ (K0Group R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩
/-- Integer scalar multiplication on `K₀(R)`, applied componentwise. -/
instance : SMul ℤ (K0Group R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- Each coefficient of the zero element of `K₀(R)` is `0`. -/
@[simp] lemma coeff_zero (k : ι) : (0 : K0Group R).coeff k = 0 := rfl
/-- Addition on `K₀(R)` is computed componentwise. -/
@[simp] lemma coeff_add (a b : K0Group R) (k : ι) :
    (a + b).coeff k = a.coeff k + b.coeff k := rfl
/-- Negation on `K₀(R)` is componentwise. -/
@[simp] lemma coeff_neg (a : K0Group R) (k : ι) :
    (-a).coeff k = -a.coeff k := rfl
/-- Subtraction on `K₀(R)` is computed componentwise. -/
@[simp] lemma coeff_sub (a b : K0Group R) (k : ι) :
    (a - b).coeff k = a.coeff k - b.coeff k := rfl

/-- `K₀(R)` is an additive abelian group with componentwise operations. -/
instance instAddCommGroup : AddCommGroup (K0Group R) where
  add_assoc a b c := by ext k; simp [add_assoc]
  zero_add a := by ext k; simp
  add_zero a := by ext k; simp
  nsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  nsmul_zero a := by ext k; simp
  nsmul_succ n a := by ext k; simp [add_mul, add_comm]
  add_comm a b := by ext k; simp [add_comm]
  neg_add_cancel a := by ext k; simp
  sub_eq_add_neg a b := by ext k; simp [sub_eq_add_neg]
  zsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  zsmul_zero' a := by ext k; simp
  zsmul_succ' n a := by ext k; simp [add_mul, add_comm]
  zsmul_neg' n a := by
    ext k
    show Int.negSucc n • a.coeff k = -((↑(n + 1) : ℤ) • a.coeff k)
    simp [Int.negSucc_eq, Nat.cast_succ]
    ring

end K0Group

/-- Left action of the Grothendieck ring of `R` on `K₀(R)` in coefficient form, defined by
`(r ◃ p)_k = Σᵢⱼ rᵢ pⱼ N_{i* k j}`. -/
def k0ActLeft (r p : ι → ℤ) : ι → ℤ :=
  fun k => univ.sum fun i => univ.sum fun j => r i * p j * (R.N (R.star i) k j : ℤ)

/-- Right action of the Grothendieck ring of `R` on `K₀(R)` in coefficient form, defined by
`(p ▹ r)_k = Σ_{a,j} pₐ rⱼ N_{k j* a}`. -/
def k0ActRight (p r : ι → ℤ) : ι → ℤ :=
  fun k => univ.sum fun a => univ.sum fun j => p a * r j * (R.N k (R.star j) a : ℤ)

/-- The involutive duality on the index set viewed as a self-equivalence of `ι`. -/
noncomputable def starEquiv : ι ≃ ι where
  toFun := R.star
  invFun := R.star
  left_inv := R.star_star
  right_inv := R.star_star

/-- Left action of the Grothendieck ring `Gr(R)` on `K₀(R)` via `k0ActLeft`. -/
instance instSMulLeft : SMul (GrRingOf R) (K0Group R) :=
  ⟨fun r m => ⟨R.k0ActLeft r.coeff m.coeff⟩⟩

/-- Coefficients of the left scalar product are computed by `k0ActLeft`. -/
@[simp] lemma smul_left_coeff (r : GrRingOf R) (m : K0Group R) (k : ι) :
    (r • m).coeff k = R.k0ActLeft r.coeff m.coeff k := rfl

/-- `K₀(R)` is a left module over the Grothendieck ring `Gr(R)`. -/
instance instModule : Module (GrRingOf R) (K0Group R) where
  one_smul m := by
    ext k
    show R.k0ActLeft R.grOne m.coeff k = m.coeff k
    rw [R.k0ActLeft_eq_grMul, R.grMul_one_left]
  mul_smul r s m := by
    ext k
    show R.k0ActLeft (R.grMul r.coeff s.coeff) m.coeff k =
         R.k0ActLeft r.coeff (R.k0ActLeft s.coeff m.coeff) k
    simp only [R.k0ActLeft_eq_grMul]
    rw [R.grMul_assoc]
  smul_zero r := by
    ext k
    show R.k0ActLeft r.coeff (fun _ => 0) k = 0
    rw [R.k0ActLeft_eq_grMul, R.grMul_zero]
  smul_add r m₁ m₂ := by
    ext k
    show R.k0ActLeft r.coeff (fun k => m₁.coeff k + m₂.coeff k) k =
         R.k0ActLeft r.coeff m₁.coeff k + R.k0ActLeft r.coeff m₂.coeff k
    simp only [R.k0ActLeft_eq_grMul]
    rw [R.grMul_left_distrib]
  add_smul r₁ r₂ m := by
    ext k
    show R.k0ActLeft (fun k => r₁.coeff k + r₂.coeff k) m.coeff k =
         R.k0ActLeft r₁.coeff m.coeff k + R.k0ActLeft r₂.coeff m.coeff k
    simp only [R.k0ActLeft_eq_grMul]
    rw [R.grMul_right_distrib]
  zero_smul m := by
    ext k
    show R.k0ActLeft (fun _ => 0) m.coeff k = 0
    rw [R.k0ActLeft_eq_grMul, R.grZero_mul]

/-- Right action of `Gr(R)ᵐᵒᵖ` on `K₀(R)` via `k0ActRight`. -/
instance instSMulRight : SMul (GrRingOf R)ᵐᵒᵖ (K0Group R) :=
  ⟨fun r m => ⟨R.k0ActRight m.coeff r.unop.coeff⟩⟩

/-- Coefficients of the right scalar product are computed by `k0ActRight`. -/
@[simp] lemma smul_right_coeff (r : (GrRingOf R)ᵐᵒᵖ) (m : K0Group R) (k : ι) :
    (r • m).coeff k = R.k0ActRight m.coeff r.unop.coeff k := rfl

/-- `K₀(R)` is a right module over the Grothendieck ring `Gr(R)`, presented as a left module
over `Gr(R)ᵐᵒᵖ`. -/
instance instModuleOp : Module (GrRingOf R)ᵐᵒᵖ (K0Group R) where
  one_smul m := by
    ext k
    show R.k0ActRight m.coeff R.grOne k = m.coeff k
    rw [R.k0ActRight_one]
  mul_smul r s m := by
    ext k

    change R.k0ActRight m.coeff (R.grMul s.unop.coeff r.unop.coeff) k =
           R.k0ActRight (R.k0ActRight m.coeff s.unop.coeff) r.unop.coeff k
    rw [← R.k0ActRight_mul_assoc]
  smul_zero r := by
    ext k
    show R.k0ActRight (fun _ => 0) r.unop.coeff k = 0
    rw [R.k0ActRight_zero_left]
  smul_add r m₁ m₂ := by
    ext k
    show R.k0ActRight (fun k => m₁.coeff k + m₂.coeff k) r.unop.coeff k =
         R.k0ActRight m₁.coeff r.unop.coeff k +
           R.k0ActRight m₂.coeff r.unop.coeff k
    rw [R.k0ActRight_add_left]
  add_smul r₁ r₂ m := by
    ext k
    show R.k0ActRight m.coeff (fun k => r₁.unop.coeff k + r₂.unop.coeff k) k =
         R.k0ActRight m.coeff r₁.unop.coeff k +
           R.k0ActRight m.coeff r₂.unop.coeff k
    rw [R.k0ActRight_add_right]
  zero_smul m := by
    ext k
    show R.k0ActRight m.coeff (fun _ => 0) k = 0
    rw [R.k0ActRight_zero_right]

/-- The left and right actions of the Grothendieck ring on `K₀(R)` commute, equipping it
with a `Gr(R)`-bimodule structure. -/
instance instSMulCommClass :
    SMulCommClass (GrRingOf R) (GrRingOf R)ᵐᵒᵖ (K0Group R) where
  smul_comm r s m := by
    ext l
    show R.k0ActLeft r.coeff (R.k0ActRight m.coeff s.unop.coeff) l =
         R.k0ActRight (R.k0ActLeft r.coeff m.coeff) s.unop.coeff l
    rw [R.k0ActLeft_eq_grMul, R.k0ActLeft_eq_grMul]
    exact congr_fun (R.k0_bimodule_compat r.coeff m.coeff s.unop.coeff) l

end K0Group
