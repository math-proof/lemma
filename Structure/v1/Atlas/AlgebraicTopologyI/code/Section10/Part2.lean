/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
public import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
public import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section10.Part4
public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace BrouwerFixedPoint

open Metric Set Inner

/-- A *retraction* of `D^n` onto `S^{n-1}`: a continuous map `r : ℝ^n → ℝ^n` sending the
disk to the sphere and fixing the boundary. Brouwer's theorem amounts to ruling out such
retractions. -/
structure IsRetraction (n : ℕ) (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop where
  continuous_r : Continuous r
  maps_to : ∀ x, x ∈ Disk n → r x ∈ Sphere n
  fixes_boundary : ∀ x, x ∈ Sphere n → r x = x


end BrouwerFixedPoint
