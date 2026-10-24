/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.BasedRings
import sympy.atlas.v1.Atlas.TensorCategories.code.BasedRings
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Finset Complex

namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)

/-- The duality involution `R.star : ι → ι` of a multifusion ring packaged as an equivalence. -/
def mfStarEquiv : ι ≃ ι where
  toFun := R.star
  invFun := R.star
  left_inv := R.star_star
  right_inv := R.star_star

noncomputable section

/-- Complexified multiplication on the Grothendieck ring of a multifusion ring,
defined via the structure constants `N i j k`. -/
def mfGrMulC (f g : ι → ℂ) : ι → ℂ :=
  fun k => ∑ i, ∑ j, f i * g j * (R.N i j k : ℂ)

/-- Complex-antilinear involution on the Grothendieck ring of a multifusion ring,
defined by complex conjugation composed with the duality involution. -/
def mfGrStarC (f : ι → ℂ) : ι → ℂ :=
  fun i => starRingEnd ℂ (f (R.star i))

/-- The trace on the complexified Grothendieck ring of a multifusion ring,
given by summing the coefficients of the unit components. -/
def mfGrTraceC (f : ι → ℂ) : ℂ := ∑ k ∈ R.I₀, f k

/-- The multiplicative identity of the complexified Grothendieck ring,
the indicator function of the set of unit components `R.I₀`. -/
def mfOneC : ι → ℂ := fun k => if k ∈ R.I₀ then 1 else 0

/-- The complexified Grothendieck ring of a multifusion ring, packaged as a structure
with a single field `coeff : ι → ℂ`. -/
@[ext]
structure MfGrRingOfC {ι : Type*} [DecidableEq ι] [Fintype ι]
    (R : MultifusionRingDef ι) where
  coeff : ι → ℂ

namespace MfGrRingOfC

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {R : MultifusionRingDef ι}

/-- Zero element of the complexified Grothendieck ring. -/
instance instZero : Zero (MfGrRingOfC R) := ⟨⟨fun _ => 0⟩⟩
/-- Multiplicative identity of the complexified Grothendieck ring, given by `R.mfOneC`. -/
instance instOne : One (MfGrRingOfC R) := ⟨⟨R.mfOneC⟩⟩

/-- Componentwise addition on the complexified Grothendieck ring. -/
instance instAdd : Add (MfGrRingOfC R) := ⟨fun a b => ⟨fun k => a.coeff k + b.coeff k⟩⟩
/-- Componentwise negation on the complexified Grothendieck ring. -/
instance instNeg : Neg (MfGrRingOfC R) := ⟨fun a => ⟨fun k => -a.coeff k⟩⟩
/-- Componentwise subtraction on the complexified Grothendieck ring. -/
instance instSub : Sub (MfGrRingOfC R) := ⟨fun a b => ⟨fun k => a.coeff k - b.coeff k⟩⟩
/-- Multiplication on the complexified Grothendieck ring via the structure constants `N`. -/
noncomputable instance instMul : Mul (MfGrRingOfC R) := ⟨fun a b => ⟨R.mfGrMulC a.coeff b.coeff⟩⟩

/-- Componentwise `ℕ`-scalar action on the complexified Grothendieck ring. -/
noncomputable instance instSMulNat : SMul ℕ (MfGrRingOfC R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩
/-- Componentwise `ℤ`-scalar action on the complexified Grothendieck ring. -/
noncomputable instance instSMulInt : SMul ℤ (MfGrRingOfC R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- Natural-number cast on the complexified Grothendieck ring: `m` is the unit `mfOneC`
scaled by `m` on the unit components. -/
instance instNatCast : NatCast (MfGrRingOfC R) :=
  ⟨fun m => ⟨fun k => if k ∈ R.I₀ then (m : ℂ) else 0⟩⟩
/-- Integer cast on the complexified Grothendieck ring: `m` is the unit scaled by `m`
on the unit components. -/
instance instIntCast : IntCast (MfGrRingOfC R) :=
  ⟨fun m => ⟨fun k => if k ∈ R.I₀ then (m : ℂ) else 0⟩⟩

/-- The coefficients of the zero element of the complexified Grothendieck ring are zero. -/
@[simp] lemma coeff_zero (k : ι) : (0 : MfGrRingOfC R).coeff k = 0 := rfl
/-- The coefficients of the unit element are `1` on `R.I₀` and `0` elsewhere. -/
@[simp] lemma coeff_one (k : ι) :
    (1 : MfGrRingOfC R).coeff k = if k ∈ R.I₀ then 1 else 0 := rfl
/-- Addition on the complexified Grothendieck ring is componentwise on coefficients. -/
@[simp] lemma coeff_add (a b : MfGrRingOfC R) (k : ι) :
    (a + b).coeff k = a.coeff k + b.coeff k := rfl
/-- Negation on the complexified Grothendieck ring is componentwise on coefficients. -/
@[simp] lemma coeff_neg (a : MfGrRingOfC R) (k : ι) :
    (-a).coeff k = -a.coeff k := rfl
/-- Subtraction on the complexified Grothendieck ring is componentwise on coefficients. -/
@[simp] lemma coeff_sub (a b : MfGrRingOfC R) (k : ι) :
    (a - b).coeff k = a.coeff k - b.coeff k := rfl

/-- The complexified Grothendieck ring of a multifusion ring is a (noncommutative) ring. -/
noncomputable instance instRing : Ring (MfGrRingOfC R) where
  add_assoc a b c := by ext k; simp [add_assoc]
  zero_add a := by ext k; simp
  add_zero a := by ext k; simp
  nsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  nsmul_zero a := by ext k; simp
  nsmul_succ n a := by ext k; simp [add_mul, add_comm]
  add_comm a b := by ext k; simp [add_comm]
  mul_assoc a b c := by
    ext k
    show (R.mfGrMulC (R.mfGrMulC a.coeff b.coeff) c.coeff) k =
         (R.mfGrMulC a.coeff (R.mfGrMulC b.coeff c.coeff)) k
    rw [R.mfGrMulC_assoc]
  one_mul a := by
    ext k
    show (R.mfGrMulC R.mfOneC a.coeff) k = a.coeff k
    rw [R.mfGrMulC_one_left]
  mul_one a := by
    ext k
    show (R.mfGrMulC a.coeff R.mfOneC) k = a.coeff k
    rw [R.mfGrMulC_one_right]
  left_distrib a b c := by
    ext k
    show (R.mfGrMulC a.coeff (fun k => b.coeff k + c.coeff k)) k =
         (R.mfGrMulC a.coeff b.coeff) k + (R.mfGrMulC a.coeff c.coeff) k
    rw [R.mfGrMulC_left_distrib]
  right_distrib a b c := by
    ext k
    show (R.mfGrMulC (fun k => a.coeff k + b.coeff k) c.coeff) k =
         (R.mfGrMulC a.coeff c.coeff) k + (R.mfGrMulC b.coeff c.coeff) k
    rw [R.mfGrMulC_right_distrib]
  zero_mul a := by
    ext k
    show (R.mfGrMulC (fun _ => 0) a.coeff) k = 0
    rw [R.mfZeroC_mul]
  mul_zero a := by
    ext k
    show (R.mfGrMulC a.coeff (fun _ => 0)) k = 0
    rw [R.mfGrMulC_zero]
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
  natCast := fun m => ⟨fun k => if k ∈ R.I₀ then (m : ℂ) else 0⟩
  natCast_zero := by ext k; simp
  natCast_succ m := by
    ext k; show (if k ∈ R.I₀ then (↑(m + 1) : ℂ) else 0) =
      (if k ∈ R.I₀ then (m : ℂ) else 0) + (if k ∈ R.I₀ then 1 else 0)
    split <;> simp
  intCast := fun m => ⟨fun k => if k ∈ R.I₀ then (m : ℂ) else 0⟩
  intCast_ofNat m := by
    ext k
    show (if k ∈ R.I₀ then (Int.ofNat m : ℂ) else 0) =
         (if k ∈ R.I₀ then (m : ℂ) else 0)
    simp [Int.cast_natCast]
  intCast_negSucc m := by
    ext k
    show (if k ∈ R.I₀ then (Int.negSucc m : ℂ) else 0) =
         -(if k ∈ R.I₀ then ((m + 1 : ℕ) : ℂ) else 0)
    split
    · simp [Int.negSucc_eq]
    · simp

/-- The ring homomorphism `ℂ →+* MfGrRingOfC R` sending `c` to the constant `c` on `R.I₀`. -/
noncomputable def algebraMapRingHom : ℂ →+* MfGrRingOfC R where
  toFun c := ⟨fun k => if k ∈ R.I₀ then c else 0⟩
  map_one' := by ext k; simp [MultifusionRingDef.mfOneC]
  map_mul' x y := by
    ext k
    change (if k ∈ R.I₀ then x * y else 0) =
         (R.mfGrMulC (fun k => if k ∈ R.I₀ then x else 0)
                   (fun k => if k ∈ R.I₀ then y else 0)) k
    rw [R.mfGrMulC_scalar_left, R.mfGrMulC_one_left]
    split <;> simp_all
  map_zero' := by ext k; simp
  map_add' x y := by
    ext k; change (if k ∈ R.I₀ then x + y else 0) =
         (if k ∈ R.I₀ then x else 0) + (if k ∈ R.I₀ then y else 0)
    split <;> simp

/-- The complexified Grothendieck ring of a multifusion ring is a `ℂ`-algebra. -/
noncomputable instance instAlgebra : Algebra ℂ (MfGrRingOfC R) where
  smul c a := ⟨fun k => c * a.coeff k⟩
  algebraMap := algebraMapRingHom
  commutes' c a := by
    ext k
    change (R.mfGrMulC (fun k => if k ∈ R.I₀ then c else 0) a.coeff) k =
         (R.mfGrMulC a.coeff (fun k => if k ∈ R.I₀ then c else 0)) k
    rw [R.mfGrMulC_scalar_left, R.mfGrMulC_one_left,
        R.mfGrMulC_scalar_right, R.mfGrMulC_one_right]
  smul_def' c a := by
    ext k
    change c * a.coeff k =
         (R.mfGrMulC (fun k => if k ∈ R.I₀ then c else 0) a.coeff) k
    rw [R.mfGrMulC_scalar_left, R.mfGrMulC_one_left]

/-- Star-ring structure on the complexified Grothendieck ring: the anti-involution
given by complex conjugation composed with duality. -/
noncomputable instance instStarRing : StarRing (MfGrRingOfC R) where
  star a := ⟨R.mfGrStarC a.coeff⟩
  star_involutive a := by
    ext k
    show R.mfGrStarC (R.mfGrStarC a.coeff) k = a.coeff k
    unfold MultifusionRingDef.mfGrStarC
    simp [R.star_star]
  star_mul a b := by
    ext k
    change R.mfGrStarC (R.mfGrMulC a.coeff b.coeff) k =
         (R.mfGrMulC (R.mfGrStarC b.coeff) (R.mfGrStarC a.coeff)) k
    unfold MultifusionRingDef.mfGrStarC MultifusionRingDef.mfGrMulC
    simp only [map_sum, map_mul, Complex.conj_natCast]
    conv_rhs =>
      rw [← Equiv.sum_comp R.mfStarEquiv]
      arg 2; ext p; rw [← Equiv.sum_comp R.mfStarEquiv]
    simp only [MultifusionRingDef.mfStarEquiv, Equiv.coe_fn_mk, R.star_star]
    conv_rhs =>
      arg 2; ext j; arg 2; ext i
      rw [show R.N (R.star j) (R.star i) k = R.N i j (R.star k) from R.mf_N_star_reverse i j k]
    rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; ring
  star_add a b := by
    ext k
    show R.mfGrStarC (fun k => a.coeff k + b.coeff k) k =
         R.mfGrStarC a.coeff k + R.mfGrStarC b.coeff k
    unfold MultifusionRingDef.mfGrStarC; simp [map_add]

/-- Compatibility of the star and the `ℂ`-scalar action on the complexified Grothendieck ring. -/
noncomputable instance instStarModule : StarModule ℂ (MfGrRingOfC R) where
  star_smul c a := by
    ext k
    show R.mfGrStarC (fun k => c * a.coeff k) k =
         (starRingEnd ℂ c) * R.mfGrStarC a.coeff k
    unfold MultifusionRingDef.mfGrStarC
    simp [map_mul]

/-- The complexified Grothendieck ring is finite-dimensional over `ℂ`. -/
noncomputable instance instFiniteDimensional : FiniteDimensional ℂ (MfGrRingOfC R) := by
  apply FiniteDimensional.of_surjective
    (show (ι → ℂ) →ₗ[ℂ] MfGrRingOfC R from
      { toFun := fun f => ⟨f⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun c f => rfl })
    (fun ⟨f⟩ => ⟨f, rfl⟩)

/-- The trace `Tr : MfGrRingOfC R →ₗ[ℂ] ℂ` as a `ℂ`-linear map. -/
noncomputable def traceLinMap : MfGrRingOfC R →ₗ[ℂ] ℂ where
  toFun a := R.mfGrTraceC a.coeff
  map_add' a b := by
    show R.mfGrTraceC (fun k => a.coeff k + b.coeff k) = R.mfGrTraceC a.coeff + R.mfGrTraceC b.coeff
    unfold MultifusionRingDef.mfGrTraceC
    rw [Finset.sum_add_distrib]
  map_smul' c a := by
    change R.mfGrTraceC (fun k => c * a.coeff k) = c * R.mfGrTraceC a.coeff
    unfold MultifusionRingDef.mfGrTraceC
    rw [Finset.mul_sum]

end MfGrRingOfC

namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)

/-- The complexified Grothendieck ring of a multifusion ring, packaged as a
`StarAlgWithTrace` with cyclic positive-definite trace pairing. -/
noncomputable def mfGrStarAlgWithTrace : StarAlgWithTrace where
  carrier := MfGrRingOfC R
  trace := MfGrRingOfC.traceLinMap
  trace_comm a b := by
    show R.mfGrTraceC (R.mfGrMulC a.coeff b.coeff) = R.mfGrTraceC (R.mfGrMulC b.coeff a.coeff)
    exact R.mf_trace_comm a.coeff b.coeff
  trace_pos_def a ha := by
    show 0 < (R.mfGrTraceC (R.mfGrMulC a.coeff (R.mfGrStarC a.coeff))).re
    apply R.mf_trace_pos_def
    intro h; apply ha; ext k; exact congrFun h k
