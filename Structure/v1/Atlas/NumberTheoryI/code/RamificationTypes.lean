/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Abbrev.v1.Atlas.NumberTheoryI.code.EisensteinRamified
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.EisensteinRamified
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Thm1023
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Cor1015
public import Theorem.v1.Atlas.NumberTheoryI.code.Thm1023
public import Abbrev.v1.Atlas.NumberTheoryI.code.Cor1015
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Def.v1.Atlas.NumberTheoryI.code.RamificationTypes
public section

open Ideal IsLocalRing


section RamificationTransitivity

variable {p e_EK e_EL e_LK : ℕ}

structure IsNthRootOfUniformizer (n : ℕ) (π : B) (πA : A) : Prop where
  uniformizer_A : Irreducible πA
  pow_eq : π ^ n = algebraMap A B πA
  adjoin_eq_top : Algebra.adjoin A ({π} : Set B) = ⊤

end RamificationTransitivity
