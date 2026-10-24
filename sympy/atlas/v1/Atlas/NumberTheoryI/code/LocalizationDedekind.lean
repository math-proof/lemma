/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalizationDedekind.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

section LocalizationPrimeIdeal

set_option linter.unusedSectionVars false

variable {A : Type*} [CommRing A] [IsDomain A]
variable (S : Submonoid A)
variable {B : Type*} [CommRing B] [Algebra A B] [IsLocalization S B]


def localization_primeIdeal_orderIso :
    { 𝔮 : Ideal B // 𝔮.IsPrime } ≃o
    { 𝔭 : Ideal A // 𝔭.IsPrime ∧ Disjoint (S : Set A) (𝔭 : Set A) } :=
  IsLocalization.orderIsoOfPrime S B

end LocalizationPrimeIdeal

noncomputable section

set_option linter.unusedSectionVars false

variable (A : Type*) [CommRing A] [IsDomain A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

def Submodule.localizedInField {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K]
    (M : Submodule A K) (S : Submonoid A) : Submodule A K where
  carrier := {x : K | ∃ m ∈ M, ∃ s ∈ S, (s : A) • x = m}
  add_mem' := by
    rintro a b ⟨ma, hma, sa, hsa, ha⟩ ⟨mb, hmb, sb, hsb, hb⟩
    exact ⟨(sb : A) • ma + (sa : A) • mb,
      M.add_mem (M.smul_mem sb hma) (M.smul_mem sa hmb),
      sa * sb, S.mul_mem hsa hsb, by
        simp only [smul_add, mul_smul]; congr 1; rw [smul_comm, ha]; rw [hb]⟩
  zero_mem' := ⟨0, M.zero_mem, 1, S.one_mem, by simp⟩
  smul_mem' := by
    intro c x ⟨m, hm, s, hs, hsx⟩
    exact ⟨(c : A) • m, M.smul_mem c hm, s, hs, by rw [smul_comm, hsx]⟩


instance Int.isDedekindDomain : IsDedekindDomain ℤ :=
  inferInstance


instance Polynomial.isDedekindDomain (k : Type*) [Field k] :
    IsDedekindDomain (Polynomial k) :=
  inferInstance

end PrincipalIdealDedekind
