/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.NumberTheoryI.code.EisensteinRamified
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.EisensteinRamified
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Thm1023
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor1015
import Theorem.v1.Atlas.NumberTheoryI.code.Thm1023
import Abbrev.v1.Atlas.NumberTheoryI.code.Cor1015
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
open Ideal IsLocalRing


section RamificationDefinitions

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

noncomputable abbrev AKLB_residueChar :=
  ringChar (IsLocalRing.ResidueField A)

end RamificationDefinitions
