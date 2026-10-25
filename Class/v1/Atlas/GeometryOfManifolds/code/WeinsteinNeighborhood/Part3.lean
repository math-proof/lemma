/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.MoserDarboux
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Structure.v1.Atlas.GeometryOfManifolds.code.MoserDarboux.Part2
import Def.v1.Atlas.GeometryOfManifolds.code.BlockMatrixLp
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.ODE.PicardLindelof
import Structure.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part6
set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- Mathlib-flavored predicate that $i : X \to M$ is a Lagrangian embedding:
$i$ is smooth and injective. -/
class IsLagrangianEmbedding_mfld
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {HH : Type*} [TopologicalSpace HH]
    (I : ModelWithCorners ℝ E HH)
    (M : Type*) [TopologicalSpace M] [ChartedSpace HH M] [IsManifold I ⊤ M]
    (X : Type*) [TopologicalSpace X] [ChartedSpace HH X] [IsManifold I ⊤ X]
    (i : X → M) : Prop where
  smooth : ContMDiff I I ⊤ i
  injective : Function.Injective i

/-- Mathlib-flavored axiomatization of $H^1(X, \mathbb{R}) = 0$ on a connected manifold:
any smooth function with zero differential is constant. -/
class HasVanishingH1_mfld
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {HH : Type*} [TopologicalSpace HH]
    (I : ModelWithCorners ℝ E HH)
    (X : Type*) [TopologicalSpace X] [ChartedSpace HH X] [IsManifold I ⊤ X] : Prop where
  connected : ConnectedSpace X
  exact_of_closed_forms : ∀ (f : X → ℝ),
    ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ f →
    (∀ x : X, mfderiv I (modelWithCornersSelf ℝ ℝ) f x = 0) →
    ∀ x y : X, f x = f y

