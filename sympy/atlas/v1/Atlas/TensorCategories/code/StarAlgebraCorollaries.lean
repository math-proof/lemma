/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import sympy.atlas.v1.Atlas.TensorCategories.code.FrobeniusPerron
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Finset Complex

namespace StarAlgWithTrace

variable (B : StarAlgWithTrace)

/-- Corollary 1.43.3: a nonzero idempotent in a finite-dimensional `*`-algebra with trace has
positive real trace. -/
end StarAlgWithTrace

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

noncomputable section

/-- The complex basis vector concentrated at index `i`. -/
def basisVecC (i : ι) : ι → ℂ :=
  fun k => if k = i then 1 else 0

/-- Iterated multiplication of `f : ι → ℂ` with itself in the complexified Grothendieck ring,
starting from the multiplicative unit at exponent 0. -/
def grPowC (R : FusionRing ι) (f : ι → ℂ) : ℕ → (ι → ℂ)
  | 0 => fun k => if k = R.unit then 1 else 0
  | n + 1 => R.grMulC (grPowC R f n) f

/-- The complexified Grothendieck ring of a fusion ring, wrapped as a structure with a single
`coeff : ι → ℂ` field. -/
@[ext]
structure GrRingOfC (R : FusionRing ι) where
  coeff : ι → ℂ

namespace GrRingOfC

variable {R : FusionRing ι}

/-- The zero element of `GrRingOfC R` has all coefficients equal to zero. -/
instance instZero : Zero (GrRingOfC R) := ⟨⟨fun _ => 0⟩⟩
/-- The unit element of `GrRingOfC R` is the indicator function of the multiplicative unit. -/
instance instOne : One (GrRingOfC R) := ⟨⟨fun k => if k = R.unit then 1 else 0⟩⟩

/-- Pointwise addition on `GrRingOfC R`. -/
instance instAdd : Add (GrRingOfC R) := ⟨fun a b => ⟨fun k => a.coeff k + b.coeff k⟩⟩
/-- Pointwise negation on `GrRingOfC R`. -/
instance instNeg : Neg (GrRingOfC R) := ⟨fun a => ⟨fun k => -a.coeff k⟩⟩
/-- Pointwise subtraction on `GrRingOfC R`. -/
instance instSub : Sub (GrRingOfC R) := ⟨fun a b => ⟨fun k => a.coeff k - b.coeff k⟩⟩
/-- Multiplication on `GrRingOfC R` given by the structure constants `R.N`. -/
instance instMul : Mul (GrRingOfC R) := ⟨fun a b => ⟨R.grMulC a.coeff b.coeff⟩⟩

/-- Pointwise natural-number scalar multiplication on `GrRingOfC R`. -/
instance instSMulNat : SMul ℕ (GrRingOfC R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩
/-- Pointwise integer scalar multiplication on `GrRingOfC R`. -/
instance instSMulInt : SMul ℤ (GrRingOfC R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- The natural-number cast in `GrRingOfC R` lives entirely at the unit index. -/
instance instNatCast : NatCast (GrRingOfC R) :=
  ⟨fun m => ⟨fun k => if k = R.unit then (m : ℂ) else 0⟩⟩
/-- The integer cast in `GrRingOfC R` lives entirely at the unit index. -/
instance instIntCast : IntCast (GrRingOfC R) :=
  ⟨fun m => ⟨fun k => if k = R.unit then (m : ℂ) else 0⟩⟩

/-- Definitional unfolding of the zero coefficient. -/
@[simp] lemma coeff_zero (k : ι) : (0 : GrRingOfC R).coeff k = 0 := rfl
/-- Definitional unfolding of the unit's coefficients. -/
@[simp] lemma coeff_one (k : ι) :
    (1 : GrRingOfC R).coeff k = if k = R.unit then 1 else 0 := rfl
/-- Coefficients distribute over addition. -/
@[simp] lemma coeff_add (a b : GrRingOfC R) (k : ι) :
    (a + b).coeff k = a.coeff k + b.coeff k := rfl
/-- Coefficients commute with negation. -/
@[simp] lemma coeff_neg (a : GrRingOfC R) (k : ι) :
    (-a).coeff k = -a.coeff k := rfl
/-- Coefficients distribute over subtraction. -/
@[simp] lemma coeff_sub (a b : GrRingOfC R) (k : ι) :
    (a - b).coeff k = a.coeff k - b.coeff k := rfl

/-- The complexified Grothendieck ring of a fusion ring is a ring. -/
instance instRing : Ring (GrRingOfC R) where
  add_assoc a b c := by ext k; simp [add_assoc]
  zero_add a := by ext k; simp
  add_zero a := by ext k; simp
  nsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  nsmul_zero a := by ext k; simp
  nsmul_succ n a := by ext k; simp [add_mul, add_comm]
  add_comm a b := by ext k; simp [add_comm]
  mul_assoc a b c := by
    ext k
    show (R.grMulC (R.grMulC a.coeff b.coeff) c.coeff) k =
         (R.grMulC a.coeff (R.grMulC b.coeff c.coeff)) k
    rw [R.grMulC_assoc]
  one_mul a := by
    ext k
    show (R.grMulC (fun k => if k = R.unit then 1 else 0) a.coeff) k = a.coeff k
    rw [R.grMulC_one_left]
  mul_one a := by
    ext k
    show (R.grMulC a.coeff (fun k => if k = R.unit then 1 else 0)) k = a.coeff k
    rw [R.grMulC_one_right]
  left_distrib a b c := by
    ext k
    show (R.grMulC a.coeff (fun k => b.coeff k + c.coeff k)) k =
         (R.grMulC a.coeff b.coeff) k + (R.grMulC a.coeff c.coeff) k
    rw [R.grMulC_left_distrib]
  right_distrib a b c := by
    ext k
    show (R.grMulC (fun k => a.coeff k + b.coeff k) c.coeff) k =
         (R.grMulC a.coeff c.coeff) k + (R.grMulC b.coeff c.coeff) k
    rw [R.grMulC_right_distrib]
  zero_mul a := by
    ext k
    show (R.grMulC (fun _ => 0) a.coeff) k = 0
    rw [R.grZeroC_mul]
  mul_zero a := by
    ext k
    show (R.grMulC a.coeff (fun _ => 0)) k = 0
    rw [R.grMulC_zero]
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
  natCast := fun m => ⟨fun k => if k = R.unit then (m : ℂ) else 0⟩
  natCast_zero := by ext k; simp
  natCast_succ m := by
    ext k; show (if k = R.unit then (↑(m + 1) : ℂ) else 0) =
      (if k = R.unit then (m : ℂ) else 0) + (if k = R.unit then 1 else 0)
    split <;> simp
  intCast := fun m => ⟨fun k => if k = R.unit then (m : ℂ) else 0⟩
  intCast_ofNat m := by
    ext k
    show (if k = R.unit then (Int.ofNat m : ℂ) else 0) =
         (if k = R.unit then (m : ℂ) else 0)
    simp [Int.cast_natCast]
  intCast_negSucc m := by
    ext k
    show (if k = R.unit then (Int.negSucc m : ℂ) else 0) =
         -(if k = R.unit then ((m + 1 : ℕ) : ℂ) else 0)
    split
    · simp [Int.negSucc_eq]
    · simp

/-- The ring homomorphism `ℂ →+* GrRingOfC R` sending a scalar `c` to the element supported
at the unit with coefficient `c`. -/
def algebraMapRingHom : ℂ →+* GrRingOfC R where
  toFun c := ⟨fun k => if k = R.unit then c else 0⟩
  map_one' := by ext k; simp
  map_mul' x y := by
    ext k
    change (if k = R.unit then x * y else 0) =
         (R.grMulC (fun k => if k = R.unit then x else 0)
                   (fun k => if k = R.unit then y else 0)) k
    rw [R.grMulC_scalar_left, R.grMulC_one_left]
    split <;> simp_all
  map_zero' := by ext k; simp
  map_add' x y := by
    ext k; change (if k = R.unit then x + y else 0) =
         (if k = R.unit then x else 0) + (if k = R.unit then y else 0)
    split <;> simp

/-- `GrRingOfC R` is a ℂ-algebra via the canonical inclusion `c ↦ c * 1`. -/
instance instAlgebra : Algebra ℂ (GrRingOfC R) where
  smul c a := ⟨fun k => c * a.coeff k⟩
  algebraMap := algebraMapRingHom
  commutes' c a := by
    ext k
    change (R.grMulC (fun k => if k = R.unit then c else 0) a.coeff) k =
         (R.grMulC a.coeff (fun k => if k = R.unit then c else 0)) k
    rw [R.grMulC_scalar_left, R.grMulC_one_left,
        R.grMulC_scalar_right, R.grMulC_one_right]
  smul_def' c a := by
    ext k
    change c * a.coeff k =
         (R.grMulC (fun k => if k = R.unit then c else 0) a.coeff) k
    rw [R.grMulC_scalar_left, R.grMulC_one_left]

/-- The star-ring structure on `GrRingOfC R` defined via the index-dualising involution
`grStarC`. -/
instance instStarRing : StarRing (GrRingOfC R) where
  star a := ⟨R.grStarC a.coeff⟩
  star_involutive a := by
    ext k
    show R.grStarC (R.grStarC a.coeff) k = a.coeff k
    unfold grStarC
    simp [R.star_star]
  star_mul a b := by
    ext k
    change R.grStarC (R.grMulC a.coeff b.coeff) k =
         (R.grMulC (R.grStarC b.coeff) (R.grStarC a.coeff)) k
    unfold grStarC grMulC


    simp only [map_sum, map_mul, Complex.conj_natCast]

    conv_rhs =>
      rw [← Equiv.sum_comp R.starEquivC]
      arg 2; ext p; rw [← Equiv.sum_comp R.starEquivC]
    simp only [starEquivC, Equiv.coe_fn_mk, R.star_star]


    conv_rhs =>
      arg 2; ext j; arg 2; ext i
      rw [show R.N (R.star j) (R.star i) k = R.N i j (R.star k) from R.N_star_reverse i j k]


    rw [Finset.sum_comm]


    congr 1; ext i; congr 1; ext j; ring
  star_add a b := by
    ext k
    show R.grStarC (fun k => a.coeff k + b.coeff k) k =
         R.grStarC a.coeff k + R.grStarC b.coeff k
    unfold grStarC; simp [map_add]

/-- The star-module compatibility on `GrRingOfC R` over ℂ: `star (c • a) = conj c • star a`. -/
instance instStarModule : StarModule ℂ (GrRingOfC R) where
  star_smul c a := by
    ext k
    show R.grStarC (fun k => c * a.coeff k) k =
         (starRingEnd ℂ c) * R.grStarC a.coeff k
    unfold grStarC
    simp [map_mul]

/-- `GrRingOfC R` is finite-dimensional as a ℂ-vector space (since `ι` is finite). -/
instance instFiniteDimensional : FiniteDimensional ℂ (GrRingOfC R) := by
  apply FiniteDimensional.of_surjective
    (show (ι → ℂ) →ₗ[ℂ] GrRingOfC R from
      { toFun := fun f => ⟨f⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun c f => rfl })
    (fun ⟨f⟩ => ⟨f, rfl⟩)

/-- The trace `GrRingOfC R →ₗ[ℂ] ℂ` reading off the coefficient at the unit. -/
def traceLinMap : GrRingOfC R →ₗ[ℂ] ℂ where
  toFun a := R.grTraceC a.coeff
  map_add' a b := by
    show R.grTraceC (fun k => a.coeff k + b.coeff k) = R.grTraceC a.coeff + R.grTraceC b.coeff
    unfold grTraceC; rfl
  map_smul' c a := by
    change R.grTraceC (fun k => c * a.coeff k) = c * R.grTraceC a.coeff
    unfold grTraceC; rfl

end GrRingOfC

/-- Package the complexified Grothendieck ring of a fusion ring as a `*`-algebra with trace,
combining the star-ring, ℂ-algebra and trace data with its positive-definiteness. -/
def grStarAlgWithTrace : StarAlgWithTrace where
  carrier := GrRingOfC R
  trace := GrRingOfC.traceLinMap
  trace_comm a b := by
    show R.grTraceC (R.grMulC a.coeff b.coeff) = R.grTraceC (R.grMulC b.coeff a.coeff)
    exact R.trace_comm_grC a.coeff b.coeff
  trace_pos_def a ha := by
    show 0 < (R.grTraceC (R.grMulC a.coeff (R.grStarC a.coeff))).re
    apply R.trace_pos_def_grC
    intro h; apply ha; ext k; exact congrFun h k
