/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Instance.v1.Atlas.NumberTheoryI.code.EtaleAlgebrasProps
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.EtaleAlgebrasProps
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.IdealNorms
public import Def.v1.Atlas.NumberTheoryI.code.IdealNorms
public import Def.v1.Atlas.NumberTheoryI.code.DifferentDiscriminant.Part2
@[expose] public section

noncomputable section

open Algebra Submodule FractionalIdeal

open scoped Matrix

universe u

section TraceDualBModule

variable {A K : Type*} {L : Type u} {B : Type*}
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]

instance imageOfB_finite [Module.Finite A B] : Module.Finite A ↥(imageOfB A L B) := by
  have : Module.Finite A ((IsScalarTower.toAlgHom A B L).toLinearMap.range) :=
    Module.Finite.range (IsScalarTower.toAlgHom A B L).toLinearMap
  convert this

end TraceDualBModule
end
