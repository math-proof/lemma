/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/CanonicalMetric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.AffineWeylBook.Part2
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
import Def.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Data.Set.Card
set_option maxHeartbeats 800000

open scoped InnerProductSpace
open Set


noncomputable section

namespace AffineCoxeter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A map $f : E \to E'$ is a similitude with respect to distances $d_1, d_2$ if there
exists a uniform scale factor $\mu$ with $d_2(f(x), f(y)) = \mu \cdot d_1(x, y)$. -/
def IsSimilitude {E' : Type*} [NormedAddCommGroup E'] (f : E → E')
    (d₁ : E → E → ℝ) (d₂ : E' → E' → ℝ) : Prop :=
  ∃ (μ : ℝ), ∀ x y : E, d₂ (f x) (f y) = μ * d₁ x y

/-- The Euclidean distance on an inner-product space: $d(x, y) = \|x - y\|$. -/
def euclideanDist (x y : E) : ℝ := ‖x - y‖

/-- A distance function is $W$-invariant if every element of the affine reflection
group acts as an isometry. -/
def IsWInvariant (W : AffineReflectionGroup E) (d : E → E → ℝ) : Prop :=
  ∀ w ∈ W.group, ∀ x y : E, d (w x) (w y) = d x y

end AffineCoxeter
end
