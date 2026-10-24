/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Ideals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Ideals

def IsIdeal (R : Type*) [Ring R] (I : Set R) : Prop :=
  (∀ a ∈ I, ∀ b ∈ I, a + b ∈ I) ∧
  (0 ∈ I) ∧
  (∀ a ∈ I, -a ∈ I) ∧
  (∀ a ∈ I, ∀ r : R, r * a ∈ I)

def principalIdeal (R : Type*) [CommRing R] (a : R) : Ideal R :=
  Ideal.span {a}

example (R : Type*) [CommRing R] (I : Ideal R) : Prop := Submodule.IsPrincipal I

instance instCommRingQuotient (R : Type*) [CommRing R] (I : Ideal R) :
    CommRing (R ⧸ I) :=
  Ideal.Quotient.commRing I
