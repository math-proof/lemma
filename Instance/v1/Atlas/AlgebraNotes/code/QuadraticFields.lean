/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/QuadraticFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.DedekindDomain.PID

@[expose] public section

open Polynomial NumberField


instance instFactIrreducibleXSqPlusFive : Fact (Irreducible (X ^ 2 + C (5 : ℚ))) := by
  constructor
  have hmonic : (X ^ 2 + C (5 : ℚ)).Monic := by
    apply Polynomial.Monic.add_of_left (monic_X_pow 2); simp
  by_contra h
  rw [hmonic.not_irreducible_iff_exists_add_mul_eq_coeff (by simp)] at h
  obtain ⟨c₁, c₂, h1, h2⟩ := h
  simp only [coeff_add, coeff_X_pow, coeff_C] at h1 h2
  norm_num at h1 h2
  have hc2 : c₂ = -c₁ := by linarith
  subst hc2; nlinarith [sq_nonneg c₁]

