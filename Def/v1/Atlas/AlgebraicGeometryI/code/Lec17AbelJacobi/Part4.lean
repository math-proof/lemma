/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec17AbelJacobi.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.ClassGroup
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec17AbelJacobi.Part3
set_option maxHeartbeats 800000


noncomputable section

namespace Lec17AbelJacobi

open AlgebraicGeometry CategoryTheory

attribute [instance] IrreducibleCompleteCurve.instCommRing
  IrreducibleCompleteCurve.instIsDomain IrreducibleCompleteCurve.instIsDedekind

/-- Composition of curve morphisms, defined contravariantly via composition of the
underlying ring maps. -/
def CurveMorphism.comp {k : Type*} [Field k]
    {X Y Z : IrreducibleCompleteCurve k}
    (g : CurveMorphism Y Z) (f : CurveMorphism X Y) :
    CurveMorphism X Z where
  ringHom := f.ringHom.comp g.ringHom

/-- A curve morphism is constant iff the underlying ring map is not injective (i.e.
collapses some function on the target curve). -/
def CurveMorphism.IsConstant {k : Type*} [Field k]
    {X Y : IrreducibleCompleteCurve k} (f : CurveMorphism X Y) : Prop :=
  ¬ Function.Injective f.ringHom

/-- A curve morphism is finite iff `X.coordinateRing` is module-finite over
`Y.coordinateRing` via `f.ringHom`. -/
def CurveMorphism.IsFinite {k : Type*} [Field k]
    {X Y : IrreducibleCompleteCurve k} (f : CurveMorphism X Y) : Prop :=
  letI : Algebra Y.coordinateRing X.coordinateRing := f.ringHom.toAlgebra
  Module.Finite Y.coordinateRing X.coordinateRing

/-- A curve morphism is an isomorphism iff its underlying ring map is bijective. -/
def CurveMorphism.IsIsomorphism {k : Type*} [Field k]
    {X Y : IrreducibleCompleteCurve k} (f : CurveMorphism X Y) : Prop :=
  Function.Bijective f.ringHom

/-- A curve morphism is birational iff its ring map is injective and every element of
`X.coordinateRing` is a fraction of elements pulled back from `Y.coordinateRing`. -/
def CurveMorphism.IsBirational {k : Type*} [Field k]
    {X Y : IrreducibleCompleteCurve k} (f : CurveMorphism X Y) : Prop :=
  Function.Injective f.ringHom ∧
  ∀ a : X.coordinateRing, ∃ (b : Y.coordinateRing) (s : Y.coordinateRing),
    s ≠ 0 ∧ f.ringHom s * a = f.ringHom b

/-- A curve is normal iff its coordinate ring is integrally closed in its field of
fractions. -/
def IrreducibleCompleteCurve.IsNormal {k : Type*} [Field k]
    (X : IrreducibleCompleteCurve k) : Prop :=
  IsIntegrallyClosed X.coordinateRing

/-- The Picard group `Pic⁰(X)` of a curve, modeled as the ideal class group of its
Dedekind coordinate ring. -/
def IrreducibleCompleteCurve.Pic0Group {k : Type*} [Field k]
    (X : IrreducibleCompleteCurve k) : Type :=
  ClassGroup X.coordinateRing

end Lec17AbelJacobi
end
