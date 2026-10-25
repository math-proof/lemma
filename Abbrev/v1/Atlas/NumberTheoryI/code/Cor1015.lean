/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1015.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.ResidueFieldFunctor
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ResidueFieldFunctor
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.HenselFactorization
import Theorem.v1.Atlas.NumberTheoryI.code.HenselFactorization
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Instance.v1.Atlas.NumberTheoryI.code.Cor1015


noncomputable section

open Polynomial IsLocalRing Ideal

section Cor_10_15

variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]

abbrev reducedMinpoly (α : B) : (ResidueField A)[X] :=
  (minpoly A α).map (residue A)

end Cor_10_15
end
