/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FrobeniusPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Def.v1.Atlas.TensorCategories.code.PerronFrobeniusProof.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.PerronFrobeniusProof
import Theorem.v1.Atlas.TensorCategories.code.FrobeniusPerron
set_option maxHeartbeats 400000


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

section MulMatrix

variable (R : FusionRing ι)

noncomputable instance : HasPerronFrobeniusProperty (Fin 1) where
  pfEigenvec := fun M hM => by
    refine ⟨M 0 0, fun _ => 1, hM 0 0, fun _ => one_pos, ?_⟩
    ext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
    subst hi
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  pfUnique := fun M _ r₁ r₂ v w hv _ hw _ => by
    exact ⟨w 0 / v 0, fun i => by
      have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
      subst hi; rw [div_mul_cancel₀ _ (ne_of_gt (hv 0))]⟩

end MulMatrix
end FusionRing
