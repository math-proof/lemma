/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Order.ModularLattice
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Instance.v1.Atlas.NumberTheoryI.code.AnalyticClassNumber.Part2
open scoped Classical

open Filter Topology Asymptotics Set MeasureTheory NumberField NNReal Complex

open NumberField.InfinitePlace NumberField.Units


noncomputable section

namespace Section19

section DirichletSeries

def dedekindZetaLocalFactor (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (s : ℂ) : ℂ :=
  ∏ᶠ (𝔭 : {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥ ∧ (p : 𝓞 K) ∈ I}),
    (1 - (Ideal.absNorm (𝔭 : Ideal (𝓞 K)) : ℂ) ^ (-s))⁻¹

def characterLocalFactor (m : ℕ) [NeZero m]
    (H : Subgroup (DirichletCharacter ℂ m)) (p : ℕ) (s : ℂ) : ℂ :=
  ∏ χ : H, (1 - (χ : DirichletCharacter ℂ m) p * (p : ℂ) ^ (-s))⁻¹

noncomputable def frobenius_f_p (m : ℕ) [NeZero m] (H : Subgroup (DirichletCharacter ℂ m))
    (p : ℕ) (_hp : Nat.Prime p) : ℕ :=
  if hcop : p.Coprime m then
    orderOf (QuotientGroup.mk' (characterAnnihilator m H) (ZMod.unitOfCoprime p hcop))
  else 1

noncomputable def frobenius_g_p (m : ℕ) [NeZero m] (H : Subgroup (DirichletCharacter ℂ m))
    (p : ℕ) (hp : Nat.Prime p) : ℕ :=
  haveI : Fintype H := Fintype.ofFinite H
  Fintype.card H / frobenius_f_p m H p hp

def evalAtUnit (m : ℕ) [NeZero m]
    (H : Subgroup (DirichletCharacter ℂ m)) (u : (ZMod m)ˣ) : H →* ℂ where
  toFun χ := (χ : DirichletCharacter ℂ m) u
  map_one' := by simp [MulChar.one_apply]
  map_mul' χ₁ χ₂ := by simp [Subgroup.coe_mul, MulChar.mul_apply]

@[reducible]
noncomputable def primes_above_fintype
    (m : ℕ) [NeZero m] (H : Subgroup (DirichletCharacter ℂ m))
    (p : ℕ) (_hp : Nat.Prime p) :
    Fintype {I : Ideal (𝓞 (fixedFieldOfCharacterSubgroup m H)) //
      I.IsPrime ∧ I ≠ ⊥ ∧ (p : 𝓞 (fixedFieldOfCharacterSubgroup m H)) ∈ I} := by
  letI K := fixedFieldOfCharacterSubgroup m H
  have ha : (p : 𝓞 K) ≠ 0 := by exact_mod_cast _hp.ne_zero
  have hfin : (Ideal.span {(p : 𝓞 K)}).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hsub : {I : Ideal (𝓞 K) | I.IsPrime ∧ I ≠ ⊥ ∧ (p : 𝓞 K) ∈ I} ⊆
      (Ideal.span {(p : 𝓞 K)}).minimalPrimes := by
    intro I ⟨hIp, _, haI⟩
    refine ⟨⟨hIp, (Ideal.span_singleton_le_iff_mem I).mpr haI⟩, fun q ⟨hqp, haq⟩ hqI => ?_⟩
    by_cases hq0 : q = ⊥
    · exact absurd (Ideal.mem_bot.mp (hq0 ▸ (Ideal.span_singleton_le_iff_mem q).mp haq)) ha
    · exact ((hqp.isMaximal hq0).eq_of_le hIp.ne_top hqI).ge
  exact (hfin.subset hsub).fintype

def dedekindZetaTerm (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℕ → ℂ :=
  LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s

end DirichletSeries
end Section19
end
