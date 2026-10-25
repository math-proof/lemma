/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section34.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section31
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
import Def.v1.Atlas.AlgebraicTopologyI.code.Section31.Part7
import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Order.Directed
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Sets.Opens
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Def.v1.Atlas.AlgebraicTopologyI.code.Section34.Part9
open CategoryTheory AlgebraicTopology TopologicalSpace SingularCohomology


noncomputable section

namespace PoincareDualityCompact

open CategoryTheory

/-- **`R`-orientability of an `n`-manifold `M`.**  A typeclass wrapping
`OrientationHomology.IsROrientable n M R`: there exists a continuous
choice of local generators of `H_n(M, M ∖ {x}; R) ≅ R` over all `x ∈ M`.
This is the standard hypothesis for compact Poincaré duality with
coefficients in `R`. -/
class IsROriented (R : Type) [CommRing R] (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : Prop where
  isROrientable : OrientationHomology.IsROrientable n M R

/-- **Existence of a fundamental class.**  For a compact `R`-oriented
`n`-manifold `M`, there exists an element of `H_n(M; R)` — the
*fundamental class* `[M]` — distinguished by its local restrictions
agreeing with the chosen `R`-orientation.  This is the classical
existence statement underlying Poincaré duality. -/
class: `PD(α) = α ⌢ [M]`.  Theorem 34.2 (the Poincaré duality

end PoincareDualityCompact
end
