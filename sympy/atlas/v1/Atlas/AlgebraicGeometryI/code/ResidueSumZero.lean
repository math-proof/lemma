/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.ResidueSum
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ResidueSum
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Kaehler.Basic

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial Finset BigOperators HahnSeries Classical
  IsDedekindDomain

universe u

variable {k : Type u} [Field k]

namespace ResidueSumZero


/-- The residue of a Laurent series over `k`: the coefficient of `t^{-1}`,
i.e. the algebraic residue at the origin. -/
noncomputable def laurentResidue (f : LaurentSeries k) : k :=
  f.coeff (-1)

/-- Additivity of the residue. -/
lemma laurentResidue_add (f g : LaurentSeries k) :
    laurentResidue (f + g) = laurentResidue f + laurentResidue g := by
  simp [laurentResidue, HahnSeries.coeff_add]

/-- The residue is `k`-linear in the scalar action. -/
lemma laurentResidue_smul (c : k) (f : LaurentSeries k) :
    laurentResidue (c • f) = c * laurentResidue f := by
  simp [laurentResidue, HahnSeries.coeff_smul, smul_eq_mul]

/-- The simple pole `c · t^{-1}`, the basic Laurent series with residue `c`. -/
noncomputable def simplePole (c : k) : LaurentSeries k :=
  HahnSeries.single (-1 : ℤ) c

/-- The residue assembled as a `k`-linear map `LaurentSeries k →ₗ[k] k`. -/
noncomputable def laurentResidueLinearMap : LaurentSeries k →ₗ[k] k where
  toFun := laurentResidue
  map_add' := laurentResidue_add
  map_smul' c f := by simp [laurentResidue_smul]


/-- An abstract partial-fraction differential: `n` simple poles at distinct
points `a_i` with residues `c_i`. The algebraic shadow of a rational
differential on `ℙ¹`. -/
structure PartialFracDiff (k : Type*) [Field k] where
  n : ℕ
  c : Fin n → k
  a : Fin n → k
  hdist : Function.Injective a

/-- The local Laurent expansion of `ω` at its `j`-th pole: a pure simple pole
with coefficient `c_j`. -/
noncomputable def PartialFracDiff.localExpansionAtPole
    (ω : PartialFracDiff k) (j : Fin ω.n) : LaurentSeries k :=
  simplePole (ω.c j)

/-- The local Laurent expansion at infinity: a simple pole with residue equal
to `−Σ c_i`, enforcing the residue theorem on `ℙ¹`. -/
noncomputable def PartialFracDiff.localExpansionAtInf
    (ω : PartialFracDiff k) : LaurentSeries k :=
  simplePole (-(∑ i, ω.c i))


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

variable (C : SmoothProperCurve k)

instance : CommRing C.A := C.instCommRingA
instance : IsDomain C.A := C.instIsDomainA
instance : IsDedekindDomain C.A := C.instIsDedekindDomainA
instance : Algebra k C.A := C.instAlgebraKA
instance : Field C.K := C.instFieldK
instance : Algebra C.A C.K := C.instAlgebraAK
instance : IsFractionRing C.A C.K := C.instIsFractionRing
instance : Algebra k C.K := C.instAlgebraKK
instance : IsScalarTower k C.A C.K := C.instIsScalarTower
