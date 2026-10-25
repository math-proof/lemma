/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.NumberTheoryI.code.LocalExtensions.Part2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.LocalExtensions
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ResidueFieldFunctor
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.UnramBridge
import Def.v1.Atlas.NumberTheoryI.code.ResidueFieldFunctor
import Theorem.v1.Atlas.NumberTheoryI.code.UnramBridge
import Mathlib.RingTheory.Invariant.Basic


noncomputable section

open Ideal Polynomial

open scoped Pointwise

section UnramifiedTotallyRamifiedDecomposition

variable
  (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L] [IsFractionRing B L]
  [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]


end UnramifiedTotallyRamifiedDecomposition
end
