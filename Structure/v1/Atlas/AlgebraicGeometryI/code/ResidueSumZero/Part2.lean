/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSum
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.ResidueSum
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Kaehler.Basic
public import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSumZero.Part3


public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial Finset BigOperators HahnSeries Classical
  IsDedekindDomain

universe u

variable {k : Type u} [Field k]

namespace ResidueSumZero

/-- A smooth proper curve over `k` packaged with its scheme, its Dedekind
coordinate ring `A`, function field `K`, and the necessary algebra/tower
instances. The algebraic data needed to state the residue theorem. -/
structure SmoothProperCurve (k : Type u) [Field k] where
  X : Scheme.{u}
  overSpecK : X.Over (Spec (.of k))
  proper : @IsProper _ _ (X ↘ (Spec (.of k)))
  smooth : @SmoothOfRelativeDimension 1 _ _ (X ↘ (Spec (.of k)))
  A : Type u
  instCommRingA : CommRing A
  instIsDomainA : IsDomain A
  instIsDedekindDomainA : IsDedekindDomain A
  instAlgebraKA : Algebra k A
  K : Type u
  instFieldK : Field K
  instAlgebraAK : Algebra A K
  instIsFractionRing : IsFractionRing A K
  instAlgebraKK : Algebra k K
  instIsScalarTower : IsScalarTower k A K

end ResidueSumZero
end
