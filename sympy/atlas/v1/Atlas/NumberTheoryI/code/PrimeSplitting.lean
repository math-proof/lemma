/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PrimeSplitting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Over

open Ideal Module

noncomputable section


section DivisibilityLiesOver

variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra A B]

def IsTotallyRamified (p : Ideal A) (P : Ideal B) : Prop :=
  Ideal.ramificationIdx p P = finrank K L

def IsUnramifiedAt (p : Ideal A) (P : Ideal B) [P.LiesOver p] : Prop :=
  Ideal.ramificationIdx p P = 1 ∧
    Algebra.IsSeparable (A ⧸ p) (B ⧸ P)

def IsInert (p : Ideal A) : Prop :=
  (Ideal.map (algebraMap A B) p).IsPrime ∧
    Ideal.inertiaDeg p (Ideal.map (algebraMap A B) p) = finrank K L

def SplitsCompletely (p : Ideal A) : Prop :=
  Finset.card (primesOverFinset p B) = finrank K L

end SplittingTerminology

end
