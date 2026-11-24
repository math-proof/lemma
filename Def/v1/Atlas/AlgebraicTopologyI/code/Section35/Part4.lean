module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Order.Cofinal
public import Mathlib.Algebra.Exact
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Instance.v1.Atlas.AlgebraicTopologyI.code.Section35.Part3
open Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace CechCohomology

open TopologicalSpace SingularCohomology CategoryTheory

variable {X : Type} [TopologicalSpace X]

/-- Continuous inclusion `U₂ ↪ U₁` of opens (with `U₂ ≤ U₁`) viewed as a
morphism in `TopCat`. -/
def opensInclusion {U₁ U₂ : Opens X} (h : U₂ ≤ U₁) :
    TopCat.of ↑U₂.1 ⟶ TopCat.of ↑U₁.1 :=
  TopCat.ofHom ⟨fun x => ⟨x.1, h x.2⟩, continuous_inclusion h⟩

end CechCohomology
