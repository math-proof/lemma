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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section37
open CategoryTheory

open CategoryTheory TopologicalSpace Limits


namespace PoincareDuality

universe u

section OpenNhdsColimit

variable {α : Type u} [TopologicalSpace α]

/-- An "indexed" open neighbourhood: a pair $(k, U)$ where $U$ is an open neighbourhood of
$A_k$. Used to interpolate between the colimits along the family $\{A_k\}$ and the colimit
along their intersection, in the proof of Lemma 37.2. -/
structure CombinedOpenNhds (A : ℕ → Set α) where
  idx : ℕ
  nhd : OpenNhdsOfSet (A idx)

end OpenNhdsColimit
end PoincareDuality
