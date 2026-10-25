/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section37.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Topology.Compactness.Compact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Comma.Final
import Mathlib.Topology.Separation.Hausdorff
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Def.v1.Atlas.AlgebraicTopologyI.code.Section37.Part3
open CategoryTheory

open CategoryTheory TopologicalSpace Limits


namespace PoincareDualityCompact

open CategoryTheory PoincareDuality

/-- Bridge identifying the `SingularCohomology.singularCohomology` module (used elsewhere in
the project) with the `relativeSingularCohomology … ∅` module used in this file, as
$R$-linear equivalence. -/
instance isROriented_toPoincareDuality (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [h : IsROriented R n M] : PoincareDuality.IsROriented R n M :=
  ⟨h.isROrientable⟩

end PoincareDualityCompact
