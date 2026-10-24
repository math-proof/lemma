/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.RingInvo
import sympy.atlas.v1.Atlas.EllipticCurves.code.TorsionEndomorphism
import Lemma.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism

section Definition121

/-- A ring anti-homomorphism `R → S`: a map that preserves addition and the multiplicative
identity, but reverses the order of multiplication, i.e. `f (a * b) = f b * f a`.
Corresponds to Definition 12.1 of Sutherland's *Elliptic Curves*. -/
structure RingAntiHom (R S : Type*) [Ring R] [Ring S] where
  toFun : R → S
  map_add : ∀ a b : R, toFun (a + b) = toFun a + toFun b
  map_one : toFun 1 = 1
  map_mul_rev : ∀ a b : R, toFun (a * b) = toFun b * toFun a

namespace RingAntiHom

variable {R S : Type*} [Ring R] [Ring S]

/-- `RingAntiHom R S` is a `FunLike` type: it coerces to its underlying function and the
coercion is injective. -/
instance : FunLike (RingAntiHom R S) R S where
  coe := RingAntiHom.toFun
  coe_injective' f g h := by cases f; cases g; congr

/-- Convert a ring homomorphism into the opposite ring `R →+* Sᵐᵒᵖ` to a ring
anti-homomorphism `R → S` by post-composing with `unop`. -/
def ofRingHomToOp (f : R →+* Sᵐᵒᵖ) : RingAntiHom R S where
  toFun r := (f r).unop
  map_add a b := by simp [_root_.map_add]
  map_one := by simp [_root_.map_one]
  map_mul_rev a b := by simp [_root_.map_mul, MulOpposite.unop_mul]

end RingAntiHom

/-- A ring involution on `R`: a ring anti-homomorphism `R → R` that is its own inverse.
This is the second half of Definition 12.1 in Sutherland's *Elliptic Curves*. -/
structure RingInvolution (R : Type*) [Ring R] extends RingAntiHom R R where
  involution : ∀ x : R, toFun (toFun x) = x

namespace RingInvolution

variable {R : Type*} [Ring R]

/-- `RingInvolution R` is a `FunLike` type: it coerces to its underlying function and the
coercion is injective. -/
instance : FunLike (RingInvolution R) R R where
  coe φ := φ.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _, _, _⟩, _⟩ := f
    obtain ⟨⟨_, _, _, _⟩, _⟩ := g
    congr

/-- Convert Mathlib's `RingInvo R` (a ring involution as a `R →+* Rᵐᵒᵖ`) to a
`RingInvolution R`. -/
def ofRingInvo (f : RingInvo R) : RingInvolution R where
  toFun r := (f r).unop
  map_add a b := by simp [_root_.map_add]
  map_one := by simp [_root_.map_one]
  map_mul_rev a b := by simp [_root_.map_mul, MulOpposite.unop_mul]
  involution x := f.involution x

end RingInvolution

end Definition121

universe u

open scoped TensorProduct

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]

section EndomorphismAlgebra

variable (E : WeierstrassCurve.Affine F)

/-- The endomorphism algebra of an elliptic curve `E`, defined as
`End(E) ⊗_ℤ ℚ`. This realises Definition 12.2 of Sutherland's *Elliptic Curves*:
`End^0(E) := End(E) ⊗_ℤ ℚ`. -/
noncomputable abbrev EndomorphismAlgebra : Type u :=
  (EndRing E) ⊗[ℤ] ℚ

/-- The endomorphism algebra `End(E) ⊗_ℤ ℚ` inherits a ring structure from the tensor
product of rings. -/
noncomputable instance EndomorphismAlgebra.instRing : Ring (EndomorphismAlgebra E) :=
  inferInstance

/-- The endomorphism algebra `End(E) ⊗_ℤ ℚ` is naturally a `ℚ`-algebra via the right tensor
factor. -/
noncomputable instance EndomorphismAlgebra.instAlgebra :
    Algebra ℚ (EndomorphismAlgebra E) :=
  Algebra.TensorProduct.rightAlgebra

/-- The canonical ring homomorphism `End(E) → End(E) ⊗_ℤ ℚ` sending an endomorphism
`α` to `α ⊗ 1`. -/
noncomputable def EndomorphismAlgebra.ofEndRing :
    (EndRing E) →+* (EndomorphismAlgebra E) :=
  Algebra.TensorProduct.includeLeftRingHom

/-- The endomorphism algebra also inherits a `ℤ`-algebra structure. -/
noncomputable instance EndomorphismAlgebra.instAlgebraInt :
    Algebra ℤ (EndomorphismAlgebra E) :=
  inferInstance

/-- The endomorphism algebra is a `ℚ`-module via its `ℚ`-algebra structure. -/
noncomputable instance EndomorphismAlgebra.instModule :
    Module ℚ (EndomorphismAlgebra E) :=
  (EndomorphismAlgebra.instAlgebra E).toModule

/-- The canonical ring homomorphism `ℚ → End(E) ⊗_ℤ ℚ`, given by the `ℚ`-algebra map. -/
noncomputable def EndomorphismAlgebra.ofRat :
    ℚ →+* (EndomorphismAlgebra E) :=
  algebraMap ℚ (EndomorphismAlgebra E)

/-- The additive group structure on the endomorphism algebra, inherited from its ring
structure. -/
noncomputable instance EndomorphismAlgebra.instAddCommGroup :
    AddCommGroup (EndomorphismAlgebra E) :=
  (EndomorphismAlgebra.instRing E).toAddCommGroup

end EndomorphismAlgebra

end WeierstrassCurve.Affine
