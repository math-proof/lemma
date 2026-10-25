/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Data.Nat.Prime.Basic
import Theorem.v1.Atlas.EllipticCurves.code.FiniteFields.Part3


section Corollary_3_13

/-- Specialization of Corollary 3.13 to `𝔽q p n`: the multiplicative group
`(𝔽q p n)ˣ` is cyclic. -/
noncomputable instance 𝔽q_units_isCyclic (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsCyclic (𝔽q p n)ˣ := by
  haveI : Fintype (𝔽q p n) := Fintype.ofFinite _
  exact finite_field_mult_isCyclic (𝔽q p n)

end Corollary_3_13
