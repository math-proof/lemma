/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Cor2328
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor2328

noncomputable section

universe u

namespace TateCohomology

open Finset CategoryTheory

section AugmentationMapAndIdeal

variable (k : Type u) [CommRing k] (G : Type u) [Group G]

def augmentationMap : MonoidAlgebra k G →ₐ[k] k :=
  MonoidAlgebra.lift k k G 1

def augmentationIdeal : Ideal (MonoidAlgebra k G) :=
  RingHom.ker (augmentationMap k G).toRingHom

end AugmentationMapAndIdeal

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]

def normMap (k : Type u) [CommRing k] (G : Type u) [Group G] [Fintype G]
    (A : Rep k G) : A →ₗ[k] A :=
  A.ρ.norm

def augmentationSubmodule (k : Type u) [CommRing k] (G : Type u) [Group G]
    (A : Rep k G) : Submodule k A :=
  Submodule.span k {x : A | ∃ (g : G) (a : A), x = A.ρ g a - a}

def GCoinvariants (k : Type u) [CommRing k] (G : Type u) [Group G]
    (A : Rep k G) : Type u :=
  A ⧸ (augmentationSubmodule k G A)

instance GCoinvariants.module (A : Rep k G) : Module k (GCoinvariants k G A) :=
  Submodule.Quotient.module _

def normImageInInvariants (A : Rep k G) : Submodule k A.ρ.invariants :=
  Submodule.comap A.ρ.invariants.subtype (LinearMap.range (normMap k G A))

def tateH0 (A : Rep k G) : Type u :=
  A.ρ.invariants ⧸ normImageInInvariants A

instance tateH0.module (A : Rep k G) : Module k (tateH0 A) :=
  Submodule.Quotient.module _

def augInKerNorm (A : Rep k G) : Submodule k (LinearMap.ker (normMap k G A)) :=
  Submodule.comap (LinearMap.ker (normMap k G A)).subtype (augmentationSubmodule k G A)

def tateMinus1 (A : Rep k G) : Type u :=
  LinearMap.ker (normMap k G A) ⧸ augInKerNorm A

instance tateMinus1.module (A : Rep k G) : Module k (tateMinus1 A) :=
  Submodule.Quotient.module _

def tateH0.mk (A : Rep k G) : A.ρ.invariants →ₗ[k] tateH0 A :=
  Submodule.mkQ _

def tateMinus1.mk (A : Rep k G) : LinearMap.ker (normMap k G A) →ₗ[k] tateMinus1 A :=
  Submodule.mkQ _

def herbrandQuotient [IsCyclic G] (A : Rep k G)
    [Fintype (tateH0 A)] [Fintype (tateMinus1 A)] : ℚ :=
  (Fintype.card (tateH0 A) : ℚ) / (Fintype.card (tateMinus1 A) : ℚ)

def tateHnAux {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]
    (A : Rep k G) : Bool → Type u
  | true  => tateH0 A
  | false => tateMinus1 A

def parityBool (n : ℤ) : Bool := n % 2 == 0

def tateHn (k : Type u) [CommRing k] (G : Type u) [Group G] [Fintype G]
    [IsCyclic G] (A : Rep k G) (n : ℤ) : Type u :=
  tateHnAux A (parityBool n)


def tateMinus1_ind_augRetract {k : Type u} [CommRing k] {G : Type u} [Group G]
    (B : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    Representation.IndV (⊥ : Subgroup G).subtype B.ρ →ₗ[k] ↑B := by
  apply Representation.Coinvariants.lift _
    (TensorProduct.lift ((LinearMap.lsmul k (↑B : Type u)) ∘ₗ
      Finsupp.linearCombination k (fun (_ : G) => (1 : k))))
  intro g
  have : g = 1 := by ext; exact Subgroup.mem_bot.mp g.2
  subst this
  rw [map_one]
  exact LinearMap.comp_id _


def tateMinus1_ind_proj1 {k : Type u} [CommRing k] {G : Type u} [Group G]
    (B : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    Representation.IndV (⊥ : Subgroup G).subtype B.ρ →ₗ[k] ↑B := by
  apply Representation.Coinvariants.lift _
    (TensorProduct.lift ((LinearMap.lsmul k (↑B : Type u)) ∘ₗ
      (Finsupp.lapply (1 : G))))
  intro g
  have : g = 1 := by ext; exact Subgroup.mem_bot.mp g.2
  subst this
  rw [map_one]
  exact LinearMap.comp_id _

def HerbrandMultiplicative [IsCyclic G] (S : ShortComplex (Rep k G)) : Prop :=
  ∀ (i₁ : Fintype (tateH0 S.X₁)) (i₂ : Fintype (tateMinus1 S.X₁))
    (i₃ : Fintype (tateH0 S.X₂)) (i₄ : Fintype (tateMinus1 S.X₂))
    (i₅ : Fintype (tateH0 S.X₃)) (i₆ : Fintype (tateMinus1 S.X₃)),
    @herbrandQuotient _ _ _ _ _ _ S.X₂ i₃ i₄ =
      @herbrandQuotient _ _ _ _ _ _ S.X₁ i₁ i₂ *
      @herbrandQuotient _ _ _ _ _ _ S.X₃ i₅ i₆

def invEquivTrivInt {G₀ : Type} [Group G₀] [Fintype G₀] :
    (Rep.trivial ℤ G₀ ℤ).ρ.invariants ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofEq _ _ (by ext x; simp [Representation.mem_invariants])).trans
    Submodule.topEquiv

lemma invEquivTrivInt_apply {G₀ : Type} [Group G₀] [Fintype G₀]
    (x : (Rep.trivial ℤ G₀ ℤ).ρ.invariants) :
    (invEquivTrivInt (G₀ := G₀)) x = x.1 := by
  simp [invEquivTrivInt, Submodule.topEquiv]

lemma map_normImage_trivInt {G₀ : Type} [Group G₀] [Fintype G₀] :
    Submodule.map (invEquivTrivInt (G₀ := G₀)).toLinearMap
      (normImageInInvariants (Rep.trivial ℤ G₀ ℤ)) =
      Submodule.span ℤ {(Fintype.card G₀ : ℤ)} := by
  ext n; simp only [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [show invEquivTrivInt.toLinearMap x = x.1 from invEquivTrivInt_apply x]
    simp only [normImageInInvariants, normMap, Submodule.mem_comap,
      Submodule.coe_subtype, LinearMap.mem_range] at hx
    obtain ⟨m, hm⟩ := hx
    rw [Submodule.mem_span_singleton]
    simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply,
      Representation.trivial_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hm
    exact ⟨m, by rw [smul_eq_mul, ← hm]; ring⟩
  · intro hn
    rw [Submodule.mem_span_singleton] at hn
    obtain ⟨c, hc⟩ := hn; rw [smul_eq_mul] at hc
    refine ⟨⟨n, by rw [Representation.mem_invariants]; intro g; simp⟩, ?_, ?_⟩
    · simp only [normImageInInvariants, normMap, Submodule.mem_comap,
        Submodule.coe_subtype, LinearMap.mem_range]
      refine ⟨c, ?_⟩
      simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply,
        Representation.trivial_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      linarith
    · exact invEquivTrivInt_apply _

def tateH0_equiv_zmod {G₀ : Type} [Group G₀] [Fintype G₀] :
    tateH0 (Rep.trivial ℤ G₀ ℤ) ≃ ZMod (Fintype.card G₀) :=
  (Submodule.Quotient.equiv _ _ invEquivTrivInt map_normImage_trivInt).toEquiv.trans
    ((Int.quotientSpanEquivZMod (Fintype.card G₀ : ℤ)).toEquiv.trans
      (Equiv.cast (by simp [Int.natAbs_natCast])))

def Rep.trivialHom {G₀ : Type*} [Monoid G₀]
    {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (f : M →ₗ[ℤ] N) :
    Rep.trivial ℤ G₀ M ⟶ Rep.trivial ℤ G₀ N :=
  Rep.ofHom ⟨f, fun g => by ext x; simp [Representation.trivial]⟩

lemma ker_normMap_trivial_finFun {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    LinearMap.ker (normMap ℤ G₀ (Rep.trivial ℤ G₀ (Fin n → ℤ))) = ⊥ := by
  ext f
  simp only [LinearMap.mem_ker, Submodule.mem_bot, normMap, Representation.norm]
  rw [LinearMap.coe_sum, Finset.sum_apply]
  simp only [Representation.trivial_apply]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  constructor
  · intro h
    ext i
    have hi := congr_fun h i
    simp only [Pi.mul_apply, Pi.zero_apply] at hi
    exact (mul_eq_zero.mp hi).elim
      (absurd · (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) id
  · intro h; rw [h]; simp


def invEquivTrivFinFun {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    (Rep.trivial ℤ G₀ (Fin n → ℤ)).ρ.invariants ≃ₗ[ℤ] (Fin n → ℤ) :=
  (LinearEquiv.ofEq _ _ (by ext x; simp [Representation.mem_invariants])).trans
    Submodule.topEquiv

lemma invEquivTrivFinFun_apply {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ)
    (x : (Rep.trivial ℤ G₀ (Fin n → ℤ)).ρ.invariants) :
    (invEquivTrivFinFun n (G₀ := G₀)) x = x.1 := by
  simp [invEquivTrivFinFun, Submodule.topEquiv]

lemma map_normImage_trivFinFun {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    Submodule.map (invEquivTrivFinFun n (G₀ := G₀)).toLinearMap
      (normImageInInvariants (Rep.trivial ℤ G₀ (Fin n → ℤ))) =
      LinearMap.range ((Fintype.card G₀ : ℤ) • LinearMap.id (R := ℤ) (M := Fin n → ℤ)) := by
  ext f
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [show (invEquivTrivFinFun n).toLinearMap x = x.1 from invEquivTrivFinFun_apply n x]
    simp only [normImageInInvariants, normMap, Submodule.mem_comap,
      Submodule.coe_subtype, LinearMap.mem_range] at hx
    obtain ⟨m, hm⟩ := hx
    refine ⟨m, ?_⟩
    ext i
    simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply,
      Representation.trivial_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hm ⊢
    exact congr_fun hm i
  · rintro ⟨c, rfl⟩
    have hmem : (↑(Fintype.card G₀) : ℤ) • c ∈ (Rep.trivial ℤ G₀ (Fin n → ℤ)).ρ.invariants := by
      rw [Representation.mem_invariants]; intro g; simp
    refine ⟨⟨(↑(Fintype.card G₀) : ℤ) • c, hmem⟩, ?_, ?_⟩
    · simp only [normImageInInvariants, normMap, Submodule.mem_comap,
        Submodule.coe_subtype, LinearMap.mem_range]
      refine ⟨c, ?_⟩
      ext i
      simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply,
        Representation.trivial_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Pi.smul_apply, smul_eq_mul]
    · exact invEquivTrivFinFun_apply n _

lemma range_smul_id_eq_pi {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    LinearMap.range ((Fintype.card G₀ : ℤ) • LinearMap.id (R := ℤ) (M := Fin n → ℤ)) =
    Submodule.pi Set.univ (fun _ : Fin n => Submodule.span ℤ {(Fintype.card G₀ : ℤ)}) := by
  ext f
  simp only [LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
    Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩ i
    exact ⟨g i, by simp [Pi.smul_apply, mul_comm]⟩
  · intro h
    choose c hc using h
    exact ⟨c, by ext i; simp only [Pi.smul_apply, smul_eq_mul]; linarith [hc i]⟩

noncomputable def tateH0_equiv_pi_zmod {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    tateH0 (Rep.trivial ℤ G₀ (Fin n → ℤ)) ≃ (Fin n → ZMod (Fintype.card G₀)) := by

  refine (Submodule.Quotient.equiv _ _ (invEquivTrivFinFun n)
    (map_normImage_trivFinFun n)).toEquiv |>.trans ?_

  rw [range_smul_id_eq_pi]

  refine (Submodule.quotientPi _).toEquiv |>.trans ?_

  exact Equiv.piCongrRight (fun _ =>
    (Int.quotientSpanEquivZMod _).toEquiv.trans
      (Equiv.cast (by simp [Int.natAbs_natCast])))

instance tateH0.finite_trivial_finFun {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    Finite (tateH0 (Rep.trivial ℤ G₀ (Fin n → ℤ))) :=
  Finite.of_equiv _ (tateH0_equiv_pi_zmod n).symm

instance tateMinus1.finite_trivial_finFun {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    Finite (tateMinus1 (Rep.trivial ℤ G₀ (Fin n → ℤ))) := by
  haveI : Subsingleton (LinearMap.ker (normMap ℤ G₀ (Rep.trivial ℤ G₀ (Fin n → ℤ)))) := by
    rw [ker_normMap_trivial_finFun n]; infer_instance
  haveI : Subsingleton (tateMinus1 (Rep.trivial ℤ G₀ (Fin n → ℤ))) :=
    Quotient.instSubsingletonQuotient _
  exact Finite.of_subsingleton

end TateCohomology
