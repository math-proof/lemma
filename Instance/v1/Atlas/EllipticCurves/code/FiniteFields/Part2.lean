/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Theorem.v1.Atlas.EllipticCurves.code.FiniteFields.Part3
@[expose] public section

section Corollary_3_13

/-- Specialization of Corollary 3.13 to `𝔽q p n`: the multiplicative group
`(𝔽q p n)ˣ` is cyclic. -/
noncomputable instance 𝔽q_units_isCyclic (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsCyclic (𝔽q p n)ˣ := by
  haveI : Fintype (𝔽q p n) := Fintype.ofFinite _
  exact finite_field_mult_isCyclic (𝔽q p n)

end Corollary_3_13
