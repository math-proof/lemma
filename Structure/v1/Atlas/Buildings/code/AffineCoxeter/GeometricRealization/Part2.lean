/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/GeometricRealization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex.Part2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Def.v1.Atlas.Buildings.code.AffineCoxeter.GeometricRealization
set_option linter.unusedSectionVars false


noncomputable section

open Finset BigOperators

/-- An abstract geometric realization of a Coxeter complex $(W, S)$: a topological space carrier
together with a $W$-indexed family of "chamber" subsets and a fundamental domain. -/
structure CoxeterComplexGeometricRealization (W : Type*) [Group W] (S : Set W) where
  carrier : Type*
  [topSpace : TopologicalSpace carrier]
  chamberMap : W → Set carrier
  fundamentalDomain : Set carrier

attribute [instance] CoxeterComplexGeometricRealization.topSpace

/-- An **affine** geometric realization: an action of $W$ by Euclidean transformations of
$\mathbb R^\iota$, together with a fundamental chamber, its $W$-translates, and the underlying
hyperplane arrangement. -/
structure AffineGeometricRealization (W : Type*) [Group W] (S : Set W)
    (ι : Type*) [Fintype ι] where
  action : W → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι
  action_mul : ∀ w₁ w₂ : W, ∀ x, action (w₁ * w₂) x = action w₁ (action w₂ x)
  action_one : ∀ x, action 1 x = x
  fundamentalChamber : Set (EuclideanSpace ℝ ι)
  chamber (w : W) : Set (EuclideanSpace ℝ ι) := action w '' fundamentalChamber
  hyperplanes : Set (Set (EuclideanSpace ℝ ι))

end
