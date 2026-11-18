module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section37.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Comma.Final
public import Mathlib.Topology.Separation.Hausdorff
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
public section
open CategoryTheory

noncomputable section

namespace PoincareDuality

variable (R : Type) [CommRing R]

/-- Relative singular cohomology $H^p(X, A; R)$ of a pair $(X, A)$ with coefficients in
$R$, as an object of `ModuleCat.{0} R`. -/
class IsROriented (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : Prop where
  isROrientable : OrientationHomology.IsROrientable n M R

end PoincareDuality
end
