/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSum
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ResidueSum
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Kaehler.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSumZero.Part3


noncomputable section

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
