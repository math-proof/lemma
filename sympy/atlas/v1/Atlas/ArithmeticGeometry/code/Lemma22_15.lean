/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Lemma22_15.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Lemma22_15

variable {Place : Type*} [DecidableEq Place]

/-- Increment a divisor $D$ by one at the place $P$, leaving all other places
unchanged. -/
def addPlace (D : Place → ℤ) (P : Place) : Place → ℤ :=
  Function.update D P (D P + 1)

/-- Abstract statement that the divisor $D$ is maximal for the relation
`omegaD ω · `: $\omega$ is associated to $D$ and every other associated divisor
$D'$ satisfies $D' \le D$. Used to formulate the unique divisor of a Weil
differential (Lemma 22.15). -/
def IsMaximalDivisorFor (omegaD : Ω → (Place → ℤ) → Prop) (ω : Ω) (D : Place → ℤ) : Prop :=
  omegaD ω D ∧ ∀ D' : Place → ℤ, omegaD ω D' → D' ≤ D
