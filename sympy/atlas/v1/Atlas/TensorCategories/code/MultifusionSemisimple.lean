/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean -/

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

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

open Finset Complex

namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (M : MultifusionRingDef ι)

noncomputable section

/-- Multiplication on the complexified multifusion Grothendieck ring: `(f * g) k =
∑_{i, j} f i * g j * N_{i,j}^k`. -/
def mfGrMulC (f g : ι → ℂ) : ι → ℂ :=
  fun k => ∑ i, ∑ j, f i * g j * (M.N i j k : ℂ)

/-- Star operation on the complexified multifusion Grothendieck ring, induced by the
involution on basis labels via complex conjugation of coordinates. -/
def mfGrStarC (f : ι → ℂ) : ι → ℂ :=
  fun i => starRingEnd ℂ (f (M.star i))

/-- Trace on the complexified multifusion Grothendieck ring: sum of the coordinates over
the set of unit basis elements `I₀`. -/
def mfGrTraceC (f : ι → ℂ) : ℂ := ∑ k ∈ M.I₀, f k

/-- The star involution on basis labels packaged as an equivalence `ι ≃ ι`. -/
def mfStarEquiv : ι ≃ ι where
  toFun := M.star
  invFun := M.star
  left_inv := M.star_star
  right_inv := M.star_star

/-- Cyclic property of the trace on the complexified Grothendieck ring. -/
structure MfGrRingOfC (M : MultifusionRingDef ι) where
  coeff : ι → ℂ

namespace MfGrRingOfC

variable {M : MultifusionRingDef ι}

/-- Zero element of `MfGrRingOfC M`: the constant-zero coordinate function. -/
instance instZero : Zero (MfGrRingOfC M) := ⟨⟨fun _ => 0⟩⟩
/-- Unit element of `MfGrRingOfC M`: the indicator function of the unit subset `I₀`. -/
instance instOne : One (MfGrRingOfC M) := ⟨⟨fun k => if k ∈ M.I₀ then 1 else 0⟩⟩

/-- Coordinate-wise addition on `MfGrRingOfC M`. -/
instance instAdd : Add (MfGrRingOfC M) := ⟨fun a b => ⟨fun k => a.coeff k + b.coeff k⟩⟩
/-- Coordinate-wise negation on `MfGrRingOfC M`. -/
instance instNeg : Neg (MfGrRingOfC M) := ⟨fun a => ⟨fun k => -a.coeff k⟩⟩
/-- Coordinate-wise subtraction on `MfGrRingOfC M`. -/
instance instSub : Sub (MfGrRingOfC M) := ⟨fun a b => ⟨fun k => a.coeff k - b.coeff k⟩⟩
/-- Multiplication on `MfGrRingOfC M` given by the structure constants via `mfGrMulC`. -/
instance instMul : Mul (MfGrRingOfC M) := ⟨fun a b => ⟨M.mfGrMulC a.coeff b.coeff⟩⟩

/-- Coordinate-wise `ℕ`-scalar multiplication on `MfGrRingOfC M`. -/
instance instSMulNat : SMul ℕ (MfGrRingOfC M) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩
/-- Coordinate-wise `ℤ`-scalar multiplication on `MfGrRingOfC M`. -/
instance instSMulInt : SMul ℤ (MfGrRingOfC M) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- Natural-number cast into `MfGrRingOfC M`: `m` becomes `m` on the unit subset and `0`
elsewhere. -/
instance instNatCast : NatCast (MfGrRingOfC M) :=
  ⟨fun m => ⟨fun k => if k ∈ M.I₀ then (m : ℂ) else 0⟩⟩
/-- Integer cast into `MfGrRingOfC M`: `m` becomes `m` on the unit subset and `0` elsewhere. -/
instance instIntCast : IntCast (MfGrRingOfC M) :=
  ⟨fun m => ⟨fun k => if k ∈ M.I₀ then (m : ℂ) else 0⟩⟩

/-- Coordinates of the zero element vanish. -/
@[simp] lemma coeff_zero (k : ι) : (0 : MfGrRingOfC M).coeff k = 0 := rfl
/-- Coordinates of the unit element are the indicator function of `I₀`. -/
@[simp] lemma coeff_one (k : ι) :
    (1 : MfGrRingOfC M).coeff k = if k ∈ M.I₀ then 1 else 0 := rfl
/-- Coordinates of a sum are the sum of coordinates. -/
@[simp] lemma coeff_add (a b : MfGrRingOfC M) (k : ι) :
    (a + b).coeff k = a.coeff k + b.coeff k := rfl
/-- Coordinates of a negation are the negation of coordinates. -/
@[simp] lemma coeff_neg (a : MfGrRingOfC M) (k : ι) :
    (-a).coeff k = -a.coeff k := rfl
/-- Coordinates of a difference are the coordinate-wise difference. -/
@[simp] lemma coeff_sub (a b : MfGrRingOfC M) (k : ι) :
    (a - b).coeff k = a.coeff k - b.coeff k := rfl

/-- Ring structure on `MfGrRingOfC M`: coordinate-wise additive group with multiplication
given by the multifusion structure constants. -/
instance instStarRing : StarRing (MfGrRingOfC M) where
  star a := ⟨M.mfGrStarC a.coeff⟩
  star_involutive a := by
    ext k
    show M.mfGrStarC (M.mfGrStarC a.coeff) k = a.coeff k
    unfold mfGrStarC
    simp [M.star_star]
  star_mul a b := by
    ext k
    change M.mfGrStarC (M.mfGrMulC a.coeff b.coeff) k =
         (M.mfGrMulC (M.mfGrStarC b.coeff) (M.mfGrStarC a.coeff)) k
    unfold mfGrStarC mfGrMulC
    simp only [map_sum, map_mul, Complex.conj_natCast]
    conv_rhs =>
      rw [← Equiv.sum_comp M.mfStarEquiv]
      arg 2; ext p; rw [← Equiv.sum_comp M.mfStarEquiv]
    simp only [mfStarEquiv, Equiv.coe_fn_mk, M.star_star]
    conv_rhs =>
      arg 2; ext j; arg 2; ext i
      rw [show M.N (M.star j) (M.star i) k = M.N i j (M.star k) from by
        rw [M.star_anti]; simp [M.star_star]]
    rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; ring
  star_add a b := by
    ext k
    show M.mfGrStarC (fun k => a.coeff k + b.coeff k) k =
         M.mfGrStarC a.coeff k + M.mfGrStarC b.coeff k
    unfold mfGrStarC; simp [map_add]

/-- Compatibility of star and scalar multiplication: `star (c • a) = (conj c) • star a`. -/
instance instStarModule : StarModule ℂ (MfGrRingOfC M) where
  star_smul c a := by
    ext k
    show M.mfGrStarC (fun k => c * a.coeff k) k =
         (starRingEnd ℂ c) * M.mfGrStarC a.coeff k
    unfold mfGrStarC
    simp [map_mul]

/-- The complexified multifusion Grothendieck ring `MfGrRingOfC M` is finite-dimensional
over `ℂ`, with dimension at most `|ι|`. -/
instance instFiniteDimensional : FiniteDimensional ℂ (MfGrRingOfC M) := by
  apply FiniteDimensional.of_surjective
    (show (ι → ℂ) →ₗ[ℂ] MfGrRingOfC M from
      { toFun := fun f => ⟨f⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun c f => rfl })
    (fun ⟨f⟩ => ⟨f, rfl⟩)

/-- The trace `mfGrTraceC` packaged as a `ℂ`-linear map `MfGrRingOfC M →ₗ[ℂ] ℂ`. -/
def mfTraceLinMap : MfGrRingOfC M →ₗ[ℂ] ℂ where
  toFun a := M.mfGrTraceC a.coeff
  map_add' a b := by
    show M.mfGrTraceC (fun k => a.coeff k + b.coeff k) = M.mfGrTraceC a.coeff + M.mfGrTraceC b.coeff
    unfold mfGrTraceC; rw [Finset.sum_add_distrib]
  map_smul' c a := by
    change M.mfGrTraceC (fun k => c * a.coeff k) = c * M.mfGrTraceC a.coeff
    unfold mfGrTraceC; rw [Finset.mul_sum]

end MfGrRingOfC

/-- The complexified multifusion Grothendieck ring assembled as a `StarAlgWithTrace`, with
the cyclic positive-definite trace `mfTraceLinMap`. -/
end

end MultifusionRingDef

/-- EGNO Corollary 1.43.5: the complexified Grothendieck ring of a multifusion ring is
semisimple. -/
