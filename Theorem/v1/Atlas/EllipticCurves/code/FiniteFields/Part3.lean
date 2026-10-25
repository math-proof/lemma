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
import Def.v1.Atlas.EllipticCurves.code.FiniteFields.Part3


section Theorem_3_6

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

open Subgroup in
/-- Theorem 3.12: every finite subgroup of the multiplicative group `kˣ` of a
field is cyclic. -/
theorem finite_mult_subgroup_of_field_isCyclic
    (k : Type*) [Field k] (G : Subgroup kˣ) [Finite G] : IsCyclic G :=
  isCyclic_subgroup_units G

end Theorem_3_12

section Corollary_3_13

/-- Corollary 3.13: the multiplicative group `kˣ` of a finite field is cyclic. -/
theorem finite_field_mult_isCyclic
    (k : Type*) [Field k] [Fintype k] : IsCyclic kˣ := by
  have : IsCyclic (⊤ : Subgroup kˣ) := finite_mult_subgroup_of_field_isCyclic k ⊤
  exact isCyclic_of_surjective Subgroup.topEquiv Subgroup.topEquiv.surjective

end Corollary_3_13
