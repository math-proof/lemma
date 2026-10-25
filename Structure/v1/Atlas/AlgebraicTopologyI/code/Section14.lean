/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section14.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section14
open Topology


namespace CWComplex

variable {X : Type*} [TopologicalSpace X]

/-- A bundle of the three properties of CW-complexes stated in Theorem 14.8:
every CW-complex is Hausdorff, compactness is equivalent to finiteness, and every
compact smooth manifold admits a CW-structure. -/
structure CWComplexProperties where
  hausdorff :
    ∀ (X : Type*) [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)], T2Space X
  compact_iff_finite :
    ∀ (X : Type*) [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)],
      CompactSpace X ↔ IsFinite X
  manifold_admits_cw :
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {H : Type*} [TopologicalSpace H]
      (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
      [ChartedSpace H M] [IsManifold I ⊤ M] [CompactSpace M],
      Topology.CWComplex (Set.univ : Set M)

end CWComplex
