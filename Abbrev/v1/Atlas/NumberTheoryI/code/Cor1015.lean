module
public import Def.v1.Atlas.NumberTheoryI.code.ResidueFieldFunctor
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.ResidueFieldFunctor
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.HenselFactorization
public import Theorem.v1.Atlas.NumberTheoryI.code.HenselFactorization
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Instance.v1.Atlas.NumberTheoryI.code.Cor1015


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1015.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
