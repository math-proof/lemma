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

open scoped Classical

open Filter Topology Asymptotics Set MeasureTheory NumberField NNReal Complex

open NumberField.InfinitePlace NumberField.Units

noncomputable section

namespace Section19

section LipschitzParametrizable

def IsLipschitzContinuous {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) : Prop :=
  ∃ K : ℝ≥0, LipschitzWith K f

def IsLipschitzParametrizable {X : Type*} [PseudoMetricSpace X] (B : Set X) (d : ℕ) : Prop :=
  ∃ (m : ℕ) (f : Fin m → ((Fin d → ℝ) → X)),
    (∀ i, ∃ K : ℝ≥0, LipschitzWith K (f i)) ∧
    B ⊆ ⋃ i, (f i) '' (Set.pi Set.univ (fun _ => Set.Icc 0 1))

def outerCubeSet {n : ℕ} (S : Set (Fin n → ℝ)) (t : ℝ) : Set (Fin n → ℤ) :=
  {v | ∃ x : Fin n → ℝ, (∀ i, (v i : ℝ) ≤ x i ∧ x i < (v i : ℝ) + 1) ∧
    (fun i => x i / t) ∈ S}

def innerCubeSet {n : ℕ} (S : Set (Fin n → ℝ)) (t : ℝ) : Set (Fin n → ℤ) :=
  {v | ∀ x : Fin n → ℝ, (∀ i, (v i : ℝ) ≤ x i ∧ x i < (v i : ℝ) + 1) →
    (fun i => x i / t) ∈ S}

noncomputable def unitCube {n : ℕ} (v : Fin n → ℤ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ico (v i : ℝ) ((v i : ℝ) + 1))

noncomputable def idealToClass (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩

noncomputable def toFinME : (NumberField.mixedEmbedding.euclidean.mixedSpace K) ≃ᵐ
    (Fin (Module.finrank ℚ K) → ℝ) := by
  classical
  have hcard : Fintype.card (NumberField.mixedEmbedding.index K) = Module.finrank ℚ K := by
    linarith [NumberField.mixedEmbedding.euclidean.finrank K,
      Module.finrank_eq_card_basis
        (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis K).toBasis]
  let onb := (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis K).reindex
    (Fintype.equivFinOfCardEq hcard)
  exact onb.measurableEquiv.trans
    (MeasurableEquiv.toLp 2 (Fin (Module.finrank ℚ K) → ℝ)).symm

end AnalyticClassNumber

section DirichletSeries

noncomputable def dirichletSeriesAbel (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  s * ∫ x in Set.Ioi (1 : ℝ), (∑ n ∈ Finset.range ⌊x⌋₊, f (n + 1)) *
    (x : ℂ) ^ (-(s + 1))

noncomputable def dirichletSeriesContinuation (a : ℕ → ℂ) (ρ : ℂ) : ℂ → ℂ :=
  fun s => ρ * riemannZeta s + dirichletSeriesAbel (fun n => a n - ρ) s

open Finset in

set_option maxHeartbeats 400000 in

def stepFnAbel (f : ℕ → ℂ) (x : ℝ) : ℂ :=
  if x > 1 then ∑ n ∈ Finset.range ⌊x⌋₊, f (n + 1) else 0

def IsUnramifiedAtPrime (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  ∀ (P : Ideal (𝓞 K)) [P.IsPrime],
    P.LiesOver (Ideal.span {(p : ℤ)}) →
    Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) P = 1

def pFreePart (m p : ℕ) : ℕ := m / p ^ padicValNat p m

lemma pFreePart_pos {m : ℕ} (hm : 0 < m) (p : ℕ) : 0 < pFreePart m p := by
  unfold pFreePart
  apply Nat.div_pos (Nat.le_of_dvd hm pow_padicValNat_dvd)
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp [padicValNat]
  · exact Nat.pos_of_ne_zero (by positivity)

instance pFreePart_neZero {m : ℕ} [NeZero m] (p : ℕ) : NeZero (pFreePart m p) :=
  ⟨(pFreePart_pos (NeZero.pos m) p).ne'⟩

noncomputable instance cyclotomicSubgroupModular (m : ℕ) [NeZero m] :
    IsModularLattice (Subgroup (CyclotomicField m ℚ ≃ₐ[ℚ] CyclotomicField m ℚ)) := by
  haveI : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero m ℚ
  have hm : 0 < m := NeZero.pos m
  have hirr := Polynomial.cyclotomic.irreducible_rat hm
  have oi := (IsCyclotomicExtension.autEquivPow (CyclotomicField m ℚ) hirr).mapSubgroup
  constructor
  intro x y z hxz
  have h := IsModularLattice.sup_inf_le_assoc_of_le (oi y) (oi.le_iff_le.mpr hxz)
  rw [← oi.map_sup, ← oi.map_inf, ← oi.map_inf, ← oi.map_sup] at h
  exact oi.le_iff_le.mp h

noncomputable instance cyclotomicIntermediateFieldModular (m : ℕ) [NeZero m] :
    IsModularLattice (IntermediateField ℚ (CyclotomicField m ℚ)) := by
  haveI : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero m ℚ
  haveI : IsGalois ℚ (CyclotomicField m ℚ) :=
    IsCyclotomicExtension.isGalois {m} ℚ (CyclotomicField m ℚ)
  have e := IsGalois.intermediateFieldEquivSubgroup (F := ℚ) (E := CyclotomicField m ℚ)
  constructor
  intro x y z hxz
  have h := IsModularLattice.sup_inf_le_assoc_of_le (e y) (e.le_iff_le.mpr hxz)
  rw [← e.map_sup, ← e.map_inf, ← e.map_inf, ← e.map_sup] at h
  exact e.le_iff_le.mp h

instance instNeZeroCastRat (m : ℕ) [NeZero m] : NeZero (m : ℚ) :=
  ⟨Nat.cast_ne_zero.mpr (NeZero.ne m)⟩

instance instIsCyclotomicExtensionCyclotomicField (m : ℕ) [NeZero m] :
    IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
  CyclotomicField.isCyclotomicExtension m ℚ

noncomputable def subgroupDualOrderIso (G : Type*) [CommGroup G] [Empty.Finite G] :
    Subgroup G ≃o (Subgroup (G →* ℂˣ))ᵒᵈ :=
  CommGroup.subgroupOrderIsoSubgroupMonoidHom G ℂ

noncomputable abbrev prop_18_40 := @subgroupDualOrderIso

set_option backward.isDefEq.respectTransparency false in

theorem subgroup_dual_card_annihilator (G : Type*) [CommGroup G] [Fintype G] (H : Subgroup G) :
    Nat.card H * Nat.card (MonoidHom.restrictHom H ℂˣ).ker = Nat.card G := by
  have hsurj := MonoidHom.restrict_surjective (G := G) ℂ H
  have hcard_G : Nat.card (G →* ℂˣ) = Nat.card G :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ
  have hcard_H : Nat.card (↥H →* ℂˣ) = Nat.card ↥H :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ↥H ℂ
  have hlagrange := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (MonoidHom.restrictHom H ℂˣ).ker
  have hquot : Nat.card ((G →* ℂˣ) ⧸ (MonoidHom.restrictHom H ℂˣ).ker) = Nat.card (↥H →* ℂˣ) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv
  rw [← hcard_G, hlagrange, hquot, hcard_H]

abbrev prop_18_40_card := @subgroup_dual_card_annihilator

set_option backward.isDefEq.respectTransparency false in

def characterAnnihilator (m : ℕ) (H : Subgroup (DirichletCharacter ℂ m)) :
    Subgroup (ZMod m)ˣ where
  carrier := {u | ∀ χ ∈ H, χ u.val = 1}
  mul_mem' {a b} ha hb χ hχ := by rw [Units.val_mul, map_mul, ha χ hχ, hb χ hχ, one_mul]
  one_mem' χ _ := by rw [Units.val_one, map_one]
  inv_mem' {a} ha χ hχ := by
    have h1 := ha χ hχ
    have h2 : χ a.val * χ a⁻¹.val = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    rw [h1, one_mul] at h2; exact h2

def galoisAnnihilator (m : ℕ) [NeZero m] (H : Subgroup (DirichletCharacter ℂ m)) :
    Subgroup ((CyclotomicField m ℚ) ≃ₐ[ℚ] (CyclotomicField m ℚ)) :=
  (characterAnnihilator m H).comap
    (IsCyclotomicExtension.Rat.galEquivZMod m (CyclotomicField m ℚ)).toMonoidHom

def fixedFieldOfCharacterSubgroup (m : ℕ) [NeZero m]
    (H : Subgroup (DirichletCharacter ℂ m)) :
    IntermediateField ℚ (CyclotomicField m ℚ) :=
  IntermediateField.fixedField (galoisAnnihilator m H)

instance instNumberFieldFixedField (m : ℕ) [NeZero m]
    (H : Subgroup (DirichletCharacter ℂ m)) :
    NumberField (fixedFieldOfCharacterSubgroup m H) :=
  NumberField.of_intermediateField _

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

noncomputable instance primesAbove_fintype (K : Type*) [Field K] [NumberField K]
    (p : Nat.Primes) :
    Fintype {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥ ∧ (↑↑p : 𝓞 K) ∈ I} := by
  classical
  set J := Ideal.span ({(↑↑p : 𝓞 K)} : Set (𝓞 K)) with hJ_def
  have hJ_ne_bot : J ≠ ⊥ := by
    rw [hJ_def, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast p.2.ne_zero
  have h_subset : ∀ (𝔭 : Ideal (𝓞 K)),
      𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ (↑↑p : 𝓞 K) ∈ 𝔭 →
      𝔭 ∈ (UniqueFactorizationMonoid.normalizedFactors J).toFinset := by
    intro 𝔭 ⟨h_prime, _, h_mem⟩
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hJ_ne_bot]
    exact ⟨h_prime, (Ideal.span_singleton_le_iff_mem 𝔭).mpr h_mem⟩
  exact Fintype.ofInjective
    (fun ⟨𝔭, h⟩ => ⟨𝔭, h_subset 𝔭 h⟩ :
      {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥ ∧ (↑↑p : 𝓞 K) ∈ I} →
      (UniqueFactorizationMonoid.normalizedFactors J).toFinset)
    (fun ⟨_, _⟩ ⟨_, _⟩ h => by simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)
