/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Prop415.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Structure.v1.Atlas.LieGroups.code.Prop415

@[expose] public section

noncomputable section

open scoped Manifold Topology

open MeasureTheory

namespace ContinuousRepresentation

variable {G : Type*} [Group G] [TopologicalSpace G]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {H : Type*} [TopologicalSpace H]

variable (I : ModelWithCorners ℝ E H)

variable [ChartedSpace H G] [LieGroup I ⊤ G]

def orbitMap (π : ContinuousRepresentation G F) (v : F) : G → F :=
  fun g => (π.toMonoidHom g) v

def IsSmoothVector (π : ContinuousRepresentation G F) (v : F) : Prop :=
  ContMDiff I (modelWithCornersSelf ℝ F) ⊤ (π.orbitMap v)

def smoothVectors (π : ContinuousRepresentation G F) : Set F :=
  { v : F | π.IsSmoothVector I v }

def IsGFiniteVector (π : ContinuousRepresentation G F) (v : F) : Prop :=
  FiniteDimensional ℂ
    (Submodule.span ℂ (Set.range (fun g : G => (π.toMonoidHom g) v)))

def gFiniteVectors (π : ContinuousRepresentation G F) : Set F :=
  { v : F | π.IsGFiniteVector v }

end ContinuousRepresentation
end
