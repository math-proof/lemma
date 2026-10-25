/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Instance.v1.Atlas.NumberTheoryI.code.EtaleAlgebrasProps
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.EtaleAlgebrasProps
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdealNorms
import Def.v1.Atlas.NumberTheoryI.code.IdealNorms


noncomputable section

open Algebra Submodule FractionalIdeal

open scoped Matrix

universe u

section TraceDualBModule

variable {A K : Type*} {L : Type u} {B : Type*}
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]

def traceDualB : FractionalIdeal (nonZeroDivisors B) L :=
  FractionalIdeal.dual A K 1

end TraceDualBModule
end
