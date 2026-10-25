/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Def.v1.Atlas.NumberTheoryI.code.Cor2328
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor2328
import Def.v1.Atlas.NumberTheoryI.code.TateCohomology.Part5


noncomputable section

universe u

namespace TateCohomology

open Finset CategoryTheory

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]

lemma ker_normMap_trivial_finFun {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    LinearMap.ker (normMap ℤ G₀ (Rep.trivial ℤ G₀ (Fin n → ℤ))) = ⊥ := by
  ext f
  simp only [LinearMap.mem_ker, Submodule.mem_bot, normMap, Representation.norm]
  rw [LinearMap.coe_sum, Finset.sum_apply]
  simp only [Representation.trivial_apply]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  constructor
  · intro h
    ext i
    have hi := congr_fun h i
    simp only [Pi.mul_apply, Pi.zero_apply] at hi
    exact (mul_eq_zero.mp hi).elim
      (absurd · (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) id
  · intro h; rw [h]; simp


end TateCohomology
end
