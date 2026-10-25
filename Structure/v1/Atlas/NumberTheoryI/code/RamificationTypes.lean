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
import Def.v1.Atlas.NumberTheoryI.code.RamificationTypes
open Ideal IsLocalRing


section RamificationTransitivity

variable {p e_EK e_EL e_LK : ℕ}

structure IsNthRootOfUniformizer (n : ℕ) (π : B) (πA : A) : Prop where
  uniformizer_A : Irreducible πA
  pow_eq : π ^ n = algebraMap A B πA
  adjoin_eq_top : Algebra.adjoin A ({π} : Set B) = ⊤

end RamificationTransitivity
