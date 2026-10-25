/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.SimpleModule.Basic
import Instance.v1.Atlas.TensorCategories.code.DistinguishedInvertible.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.DistinguishedInvertible
import Structure.v1.Atlas.TensorCategories.code.IntegralsDefs
set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra
open scoped TensorProduct

universe u v w


section IntegralDefs

variable (R : Type u) [CommSemiring R] (H : Type v) [Semiring H] [Algebra R H] [Coalgebra R H]

/-- Unfolded form of Definition 1.52.1 for left integrals: `∀ x, x * I = ε(x) • I`. -/
def Def_1_52_1_IsLeftIntegral (I : H) : Prop :=
  ∀ x : H, x * I = Coalgebra.counit (R := R) x • I

/-- Unfolded form of Definition 1.52.1 for right integrals: `∀ x, I * x = ε(x) • I`. -/
def Def_1_52_1_IsRightIntegral (I : H) : Prop :=
  ∀ x : H, I * x = Coalgebra.counit (R := R) x • I

/-- The `k`-submodule of left integrals in `H`. -/
def leftIntSubmodule : Submodule k H where
  carrier := { I : H | IsLeftIntegral k H I }
  add_mem' := by
    intro a b ha hb; exact ⟨fun x => by
      rw [mul_add, ha.left_integral x, hb.left_integral x, smul_add]⟩
  zero_mem' := ⟨fun _ => by simp⟩
  smul_mem' := by
    intro r I hI; exact ⟨fun x => by
      rw [mul_smul_comm, hI.left_integral x, smul_comm]⟩

/-- The `k`-submodule of right integrals in `H`. -/
def rightIntSubmodule : Submodule k H where
  carrier := { I : H | IsRightIntegral k H I }
  add_mem' := by
    intro a b ha hb; exact ⟨fun x => by
      rw [add_mul, ha.right_integral x, hb.right_integral x, smul_add]⟩
  zero_mem' := ⟨fun _ => by simp⟩
  smul_mem' := by
    intro r I hI; exact ⟨fun x => by
      rw [smul_mul_assoc, hI.right_integral x, smul_comm]⟩

end IntegralDefs
