/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.FrobeniusPerron
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs

set_option maxHeartbeats 800000

open Finset

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- The underlying integer-valued function space `ι → ℤ` of the Grothendieck ring on basis
`ι`. Elements are interpreted as formal `ℤ`-linear combinations of basis vectors. -/
def GrRing (ι : Type*) [DecidableEq ι] [Fintype ι] := ι → ℤ

/-- Multiplication on `GrRing ι` defined by the fusion structure constants `N i j k`,
implementing `X_i X_j = ∑_k N_{ij}^k X_k`. -/
def grMul (f g : GrRing ι) : GrRing ι :=
  fun k => univ.sum fun i => univ.sum fun j => f i * g j * (R.N i j k : ℤ)

/-- The multiplicative identity of `GrRing ι`: the indicator function of the unit basis element. -/
def grOne : GrRing ι := fun k => if k = R.unit then 1 else 0

/-- Bundled form of the Grothendieck ring of a fusion ring `R`: an element is identified
with its integer-valued coefficient function on the basis. -/
@[ext]
structure GrRingOf (R : FusionRing ι) where
  coeff : ι → ℤ

namespace GrRingOf

variable {R : FusionRing ι}

/-- Zero element of `GrRingOf R`. -/
instance : Zero (GrRingOf R) := ⟨⟨fun _ => 0⟩⟩
/-- Multiplicative identity of `GrRingOf R`, given by `R.grOne`. -/
instance : One (GrRingOf R) := ⟨⟨R.grOne⟩⟩

/-- Pointwise addition on `GrRingOf R`. -/
instance : Add (GrRingOf R) := ⟨fun a b => ⟨fun k => a.coeff k + b.coeff k⟩⟩
/-- Pointwise negation on `GrRingOf R`. -/
instance : Neg (GrRingOf R) := ⟨fun a => ⟨fun k => -a.coeff k⟩⟩
/-- Pointwise subtraction on `GrRingOf R`. -/
instance : Sub (GrRingOf R) := ⟨fun a b => ⟨fun k => a.coeff k - b.coeff k⟩⟩
/-- Fusion multiplication on `GrRingOf R`. -/
instance : Mul (GrRingOf R) := ⟨fun a b => ⟨R.grMul a.coeff b.coeff⟩⟩

/-- Pointwise `ℕ`-scalar multiplication on `GrRingOf R`. -/
instance : SMul ℕ (GrRingOf R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩
/-- Pointwise `ℤ`-scalar multiplication on `GrRingOf R`. -/
instance : SMul ℤ (GrRingOf R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- Embedding of `ℕ` into `GrRingOf R` as multiples of the unit basis element. -/
instance : NatCast (GrRingOf R) := ⟨fun m => ⟨fun k => if k = R.unit then (m : ℤ) else 0⟩⟩
/-- Embedding of `ℤ` into `GrRingOf R` as multiples of the unit basis element. -/
instance : IntCast (GrRingOf R) := ⟨fun m => ⟨fun k => if k = R.unit then (m : ℤ) else 0⟩⟩

/-- The coefficient of the zero element is zero. -/
@[simp] lemma coeff_zero (k : ι) : (0 : GrRingOf R).coeff k = 0 := rfl
/-- Coefficients distribute over addition. -/
@[simp] lemma coeff_add (a b : GrRingOf R) (k : ι) :
    (a + b).coeff k = a.coeff k + b.coeff k := rfl
/-- Coefficients distribute over negation. -/
@[simp] lemma coeff_neg (a : GrRingOf R) (k : ι) :
    (-a).coeff k = -a.coeff k := rfl
/-- Coefficients distribute over subtraction. -/
@[simp] lemma coeff_sub (a b : GrRingOf R) (k : ι) :
    (a - b).coeff k = a.coeff k - b.coeff k := rfl

/-- The Grothendieck ring `GrRingOf R` of a fusion ring `R` is a `Ring`. -/
instance instRing : Ring (GrRingOf R) where
  add_assoc a b c := by ext k; simp [add_assoc]
  zero_add a := by ext k; simp
  add_zero a := by ext k; simp
  nsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  nsmul_zero a := by ext k; simp
  nsmul_succ n a := by ext k; simp [add_mul, add_comm]
  add_comm a b := by ext k; simp [add_comm]
  mul_assoc a b c := by
    ext k
    show (R.grMul (R.grMul a.coeff b.coeff) c.coeff) k =
         (R.grMul a.coeff (R.grMul b.coeff c.coeff)) k
    rw [R.grMul_assoc]
  one_mul a := by
    ext k
    show (R.grMul R.grOne a.coeff) k = a.coeff k
    rw [R.grMul_one_left]
  mul_one a := by
    ext k
    show (R.grMul a.coeff R.grOne) k = a.coeff k
    rw [R.grMul_one_right]
  left_distrib a b c := by
    ext k
    show (R.grMul a.coeff (fun k => b.coeff k + c.coeff k)) k =
         (R.grMul a.coeff b.coeff) k + (R.grMul a.coeff c.coeff) k
    rw [R.grMul_left_distrib]
  right_distrib a b c := by
    ext k
    show (R.grMul (fun k => a.coeff k + b.coeff k) c.coeff) k =
         (R.grMul a.coeff c.coeff) k + (R.grMul b.coeff c.coeff) k
    rw [R.grMul_right_distrib]
  zero_mul a := by
    ext k
    show (R.grMul (fun _ => 0) a.coeff) k = 0
    rw [R.grZero_mul]
  mul_zero a := by
    ext k
    show (R.grMul a.coeff (fun _ => 0)) k = 0
    rw [R.grMul_zero]
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
  natCast := fun m => ⟨fun k => if k = R.unit then (m : ℤ) else 0⟩
  natCast_zero := by
    ext k
    show (if k = R.unit then (0 : ℤ) else 0) = 0
    split <;> rfl
  natCast_succ m := by
    ext k
    show (if k = R.unit then ((m + 1 : ℕ) : ℤ) else 0) =
         (if k = R.unit then (m : ℤ) else 0) + (if k = R.unit then 1 else 0)
    split <;> simp
  intCast := fun m => ⟨fun k => if k = R.unit then (m : ℤ) else 0⟩
  intCast_ofNat m := by ext k; rfl
  intCast_negSucc m := by
    ext k
    show (if k = R.unit then (Int.negSucc m : ℤ) else 0) =
         -(if k = R.unit then ((m + 1 : ℕ) : ℤ) else 0)
    split <;> simp [Int.negSucc_eq]

end GrRingOf

/-- The basis vector indexed by `i ∈ ι`, given by the indicator function of `{i}`. -/
def basisVec (i : ι) : GrRing ι :=
  fun k => if k = i then 1 else 0

/-- A homomorphism of fusion rings, represented combinatorially by an integer matrix `M`
on the bases satisfying unit-preservation and a fusion-multiplication identity. -/
structure FusionRingHom
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (R : FusionRing ι) (S : FusionRing κ) where
  M : ι → κ → ℤ
  map_unit : ∀ l, M R.unit l = if l = S.unit then 1 else 0
  map_mul : ∀ i j l,
    (Finset.univ.sum fun k => (R.N i j k : ℤ) * M k l) =
    (Finset.univ.sum fun p => Finset.univ.sum fun q => M i p * M j q * (S.N p q l : ℤ))

/-- The integer-valued action of a `FusionRingHom` on `GrRing` elements: linear extension
of the matrix `φ.M` along the basis. -/
def FusionRingHom.grMap
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {R : FusionRing ι} {S : FusionRing κ}
    (φ : FusionRingHom R S) (f : GrRing ι) : GrRing κ :=
  fun l => Finset.univ.sum fun i => f i * φ.M i l

/-- The ring homomorphism `GrRingOf R →+* GrRingOf S` induced by a `FusionRingHom`. -/
def FusionRingHom.inducedRingHom
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {R : FusionRing ι} {S : FusionRing κ}
    (φ : FusionRingHom R S) :
    GrRingOf R →+* GrRingOf S where
  toFun a := ⟨φ.grMap a.coeff⟩
  map_one' := by
    ext l; show φ.grMap R.grOne l = S.grOne l
    rw [φ.grMap_one]
  map_mul' a b := by
    ext l
    show φ.grMap (R.grMul a.coeff b.coeff) l = S.grMul (φ.grMap a.coeff) (φ.grMap b.coeff) l
    rw [φ.grMap_mul]
  map_zero' := by
    ext l; show (Finset.univ.sum fun i => (0 : GrRingOf R).coeff i * φ.M i l) = 0
    simp
  map_add' a b := by
    ext l
    show φ.grMap (fun k => a.coeff k + b.coeff k) l =
         φ.grMap a.coeff l + φ.grMap b.coeff l
    rw [φ.grMap_add]

end FusionRing

/-- The fusion ring of representations of `ℤ/2`, with basis `Fin 2` and product
given by addition modulo 2. -/
def repZ2 : FusionRing (Fin 2) where
  unit := 0
  N i j k := if (i.val + j.val) % 2 = k.val then 1 else 0
  star := id
  star_star := by decide
  unit_mul := by decide
  mul_unit := by decide
  duality := by decide
  assoc := by decide
  N_star_transpose := by decide

namespace repZ2

open FusionRing

example : Ring (GrRingOf repZ2) := inferInstance

example : (1 : GrRingOf repZ2) = ⟨repZ2.grOne⟩ := rfl

end repZ2
