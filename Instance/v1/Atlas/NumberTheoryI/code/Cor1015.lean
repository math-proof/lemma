module
public import Def.v1.Atlas.NumberTheoryI.code.ResidueFieldFunctor
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.ResidueFieldFunctor
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.HenselFactorization
public import Theorem.v1.Atlas.NumberTheoryI.code.HenselFactorization
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots


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

instance Module.IsTorsionFree.of_noZeroSMulDivisors
    {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [NoZeroSMulDivisors A B] : Module.IsTorsionFree A B where
  isSMulRegular r hr a b hab := by
    have hsub : r • (a - b) = 0 := by rw [smul_sub, sub_eq_zero]; exact hab
    rcases NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero hsub with hr0 | hab0
    · exfalso
      have : r ≠ 0 := by
        intro h; have := hr.left (show r * 1 = r * 0 by simp [h]); simp at this
      exact this hr0
    · exact sub_eq_zero.mp hab0

end
