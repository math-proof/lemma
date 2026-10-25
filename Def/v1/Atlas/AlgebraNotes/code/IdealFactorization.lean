/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/IdealFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.ClassNumber
import Instance.v1.Atlas.AlgebraNotes.code.IdealFactorization


namespace IdealFactorization

open UniqueFactorizationMonoid NumberField

noncomputable def idealNorm {d : ℤ} [IsDomain (ℤ√d)] [IsDedekindDomain (ℤ√d)]
    [Module.Free ℤ (ℤ√d)] (I : Ideal (ℤ√d)) : ℕ :=
  Ideal.absNorm I

end IdealFactorization
