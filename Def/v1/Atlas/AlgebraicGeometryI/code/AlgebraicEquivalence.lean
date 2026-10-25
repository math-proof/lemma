/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AlgebraicEquivalence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Connected.Basic


noncomputable section

namespace AlgebraicEquivalence

open AlgebraicGeometry CategoryTheory Limits

universe u


/-- A simplified placeholder model for the Cartier divisor group on `X`: integer-valued functions
on the underlying points. -/
def CartierDivisorGroup (X : Scheme.{u}) : Type u := X.carrier → ℤ

end AlgebraicEquivalence
end
