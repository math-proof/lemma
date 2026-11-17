module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sheaves.Sheaf
public section

open AlgebraicGeometry CategoryTheory TopologicalSpace


noncomputable section

universe u

/-- Definition 3: An algebraic variety over `k` is a scheme `X` with a morphism `f : X → Spec k`
that is locally of finite type, quasicompact, and whose total space is reduced. -/
class Definition3_AlgebraicVariety (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) : Prop where
  locallyOfFiniteType : LocallyOfFiniteType f
  quasiCompact : QuasiCompact f
  reduced : AlgebraicGeometry.IsReduced X

end
