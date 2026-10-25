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
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section31.Part3
open Topology MulAction CategoryTheory TopologicalSpace

open CategoryTheory AlgebraicTopology SingularCohomology Limits


noncomputable section

namespace OrientationHomology

noncomputable section

/-- The representation of `π₁(B, b)` on the fiber `F(b)` of a local coefficient
system `F`. -/
def fiberRepresentation {B : Type*} [TopologicalSpace B]
    (R : Type*) [CommRing R] (b : B)
    (F : LocalCoefficientSystem B R) :
    Representation R (FundamentalGroup B b)
      (F.obj (FundamentalGroupoid.mk b)) where
  toFun g := (F.map g).hom
  map_one' := by
    have h : (1 : FundamentalGroup B b) = 𝟙 (FundamentalGroupoid.mk b) := End.one_def
    rw [h, F.map_id]; ext; rfl
  map_mul' g₁ g₂ := by
    have h : (g₁ * g₂ : FundamentalGroup B b) = (g₂ ≫ g₁ : End (FundamentalGroupoid.mk b)) :=
      End.mul_def g₁ g₂
    rw [h, F.map_comp]; ext; rfl

/-- A natural transformation `η : F → G` of local coefficient systems restricts on
fibers to an intertwining map between the corresponding `π₁(B, b)`-representations. -/
def fiberIntertwiningMap {B : Type*} [TopologicalSpace B]
    (R : Type*) [CommRing R] (b : B)
    {F G : LocalCoefficientSystem B R} (η : F ⟶ G) :
    (fiberRepresentation R b F).IntertwiningMap (fiberRepresentation R b G) :=
  Representation.IntertwiningMap.mk (η.app (FundamentalGroupoid.mk b)).hom (fun g => by
    ext x
    simp only [fiberRepresentation, LinearMap.comp_apply]
    exact congr_fun (congrArg DFunLike.coe
      (congr_arg ModuleCat.Hom.hom (η.naturality g))) x)

/-- The functor sending a local coefficient system to its fiber at `b` as an object of
`Rep R (π₁(B, b))`. -/
def fiberToRep {B : Type*} [TopologicalSpace B]
    (R : Type*) [CommRing R] (b : B) :
    LocalCoefficientSystem B R ⥤ Rep.{0} R (FundamentalGroup B b) where
  obj F := Rep.of (fiberRepresentation R b F)
  map η := Rep.ofHom (fiberIntertwiningMap R b η)
  map_id F := by apply Rep.hom_ext; ext; rfl
  map_comp {F G H} η θ := by apply Rep.hom_ext; ext; rfl

/-- The composite "fiber" functor from local coefficient systems on `B` to modules over
the group algebra `R[π₁(B, b)]`. -/
def fiberFunctor {B : Type*} [TopologicalSpace B]
    (R : Type*) [CommRing R] (b : B) :
    LocalCoefficientSystem B R ⥤
      ModuleCat.{0} (MonoidAlgebra R (FundamentalGroup B b)) :=
  fiberToRep R b ⋙ Rep.toModuleMonoidAlgebra


end
end OrientationHomology
end
