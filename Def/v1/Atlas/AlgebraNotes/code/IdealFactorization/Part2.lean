/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/IdealFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Instance.v1.Atlas.AlgebraNotes.code.IdealFactorization.Part2

@[expose] public section

namespace IdealFactorization

open UniqueFactorizationMonoid NumberField

def IdealsSimilar {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (I J : Ideal R) : Prop :=
  ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ Ideal.span {a} * I = Ideal.span {b} * J

end IdealFactorization
