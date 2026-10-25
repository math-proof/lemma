/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section32
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Lemma32_4
import Def.v1.Atlas.AlgebraicTopologyI.code.Section32.Part2
import Def.v1.Atlas.AlgebraicTopologyI.code.Lemma32_4
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.LocallyConstant.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section31.Part6
open Topology MulAction CategoryTheory TopologicalSpace

open CategoryTheory AlgebraicTopology SingularCohomology Limits


noncomputable section

namespace OrientationHomology

/-- A *local coefficient system of `R`-modules over `B`*: a functor from the
fundamental groupoid of `B` to `R`-modules. -/
abbrev LocalCoefficientSystem (B : Type*) [TopologicalSpace B]
    (R : Type*) [CommRing R] :=
  FundamentalGroupoid B ⥤ ModuleCat.{0} R

end OrientationHomology
end
