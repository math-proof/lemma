import Lemma.Definitions.Def_FLTPrelim_Ramification
import Lemma.Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option autoImplicit false

noncomputable section

namespace ModularCurve

abbrev HeckeAlg : Type := MvPolynomial Nat.Primes ℤ

def heckeGen (ℓ : Nat.Primes) : HeckeAlg := MvPolynomial.X ℓ

@[simp] lemma aeval_heckeGen {A : Type*} [CommSemiring A] [Algebra ℤ A]
    (a : Nat.Primes → A) (ℓ : Nat.Primes) :
    MvPolynomial.aeval a (heckeGen ℓ) = a ℓ :=
  MvPolynomial.aeval_X a ℓ

lemma adjoin_range_heckeGen : Algebra.adjoin ℤ (Set.range heckeGen) = ⊤ :=
  MvPolynomial.adjoin_range_X

section EigenIdeal

variable {k : Type*} [CommRing k]

def eigenIdeal (a : Nat.Primes → k) : Ideal HeckeAlg :=
  RingHom.ker (MvPolynomial.aeval (R := ℤ) a)

lemma mem_eigenIdeal_iff (a : Nat.Primes → k) (t : HeckeAlg) :
    t ∈ eigenIdeal a ↔ MvPolynomial.aeval a t = 0 :=
  RingHom.mem_ker

lemma heckeGen_sub_mem_eigenIdeal (a : Nat.Primes → k) (ℓ : Nat.Primes) (b : ℤ)
    (hb : algebraMap ℤ k b = a ℓ) :
    heckeGen ℓ - MvPolynomial.C b ∈ eigenIdeal a := by
  rw [mem_eigenIdeal_iff, map_sub, aeval_heckeGen, MvPolynomial.aeval_C, hb, sub_self]

end EigenIdeal

section Divisorial

variable {G : Type*} [Group G] (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction G J] [SMulCommClass G HeckeAlg J]

abbrev heckeTorsion (𝔪 : Ideal HeckeAlg) : Submodule HeckeAlg J :=
  Submodule.torsionBySet HeckeAlg J (𝔪 : Set HeckeAlg)

lemma mem_heckeTorsion_iff (𝔪 : Ideal HeckeAlg) (x : J) :
    x ∈ heckeTorsion J 𝔪 ↔ ∀ t ∈ 𝔪, t • x = 0 := by
  rw [Submodule.mem_torsionBySet_iff]
  exact ⟨fun h t ht => h ⟨t, ht⟩, fun h t => h t.1 t.2⟩

theorem smul_mem_heckeTorsion {𝔪 : Ideal HeckeAlg} (g : G) {x : J}
    (hx : x ∈ heckeTorsion J 𝔪) : g • x ∈ heckeTorsion J 𝔪 := by
  rw [Submodule.mem_torsionBySet_iff] at hx ⊢
  intro t
  rw [← smul_comm g (t : HeckeAlg) x, hx t, smul_zero]

def mTorsionGaloisRep (𝔪 : Ideal HeckeAlg) :
    G →* Module.End (HeckeAlg ⧸ 𝔪) (heckeTorsion J 𝔪) where
  toFun g :=
    { toFun := fun x => ⟨g • (x : J), smul_mem_heckeTorsion J g x.2⟩
      map_add' := fun x y => by
        ext
        simp [smul_add]
      map_smul' := fun r x => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        ext
        simp only [Submodule.torsionBySet.mk_smul, RingHom.id_apply, Submodule.coe_smul]
        exact smul_comm g a (x : J) }
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [mul_smul]

@[simp] theorem coe_mTorsionGaloisRep_apply (𝔪 : Ideal HeckeAlg) (g : G)
    (x : heckeTorsion J 𝔪) :
    ((mTorsionGaloisRep J 𝔪 g x : heckeTorsion J 𝔪) : J) = g • (x : J) := rfl

def eisensteinKernel (I : Ideal HeckeAlg) : Ideal HeckeAlg where
  carrier := {t | ∃ i ∈ I, ∀ x : J, ((1 + i) * t) • x = 0}
  zero_mem' := ⟨0, I.zero_mem, fun x => by simp⟩
  add_mem' := by
    rintro t t' ⟨i, hi, ht⟩ ⟨i', hi', ht'⟩
    refine ⟨i + i' + i * i', I.add_mem (I.add_mem hi hi') (I.mul_mem_left i hi'), fun x => ?_⟩
    have h1 : ((1 + i') * ((1 + i) * t)) • x = 0 := by rw [mul_smul, ht x, smul_zero]
    have h2 : ((1 + i) * ((1 + i') * t')) • x = 0 := by rw [mul_smul, ht' x, smul_zero]
    have : (1 + (i + i' + i * i')) * (t + t')
        = (1 + i') * ((1 + i) * t) + (1 + i) * ((1 + i') * t') := by
      ring
    rw [this, add_smul, h1, h2, add_zero]
  smul_mem' := by
    rintro c t ⟨i, hi, ht⟩
    refine ⟨i, hi, fun x => ?_⟩
    have : (1 + i) * (c • t) = c * ((1 + i) * t) := by rw [smul_eq_mul]; ring
    rw [this, mul_smul, ht x, smul_zero]

def EisensteinQuotientInvariantsFinite (I : Ideal HeckeAlg) : Prop :=
  Set.Finite ((eisensteinKernel J I • (⊤ : Submodule HeckeAlg J)).mkQ ''
    {x : J | ∀ σ : G, σ • x - x ∈ eisensteinKernel J I • (⊤ : Submodule HeckeAlg J)})

end Divisorial

section Forms

variable (𝕋 : Type*) [CommRing 𝕋] (J : Type*) [AddCommGroup J] [Module 𝕋 J] (𝔪 : Ideal 𝕋)

def MTorsionNeBot : Prop :=
  Submodule.torsionBySet 𝕋 J 𝔪 ≠ ⊥

end Forms

section LocalClauses

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) HeckeAlg J]

def UnramifiedOutside : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p →
    ∀ A : ValuationSubring L, A.LiesOverPrime ℓ →
      ∀ σ ∈ A.inertiaSubgroupIn K, ∀ x : J, (∃ n : ℕ, p ^ n • x = 0) → σ • x = x

def FrobeniusQuadratic : Prop :=
  ∀ ℓ : ℕ, (hℓ : ℓ.Prime) → ¬ ℓ ∣ N * p →
    ∀ A : ValuationSubring L, A.LiesOverPrime ℓ →
      ∀ σ : L ≃ₐ[K] L, A.IsFrobeniusAt σ ℓ →
        ∀ x : J, (∃ n : ℕ, p ^ n • x = 0) →
          σ • σ • x - heckeGen ⟨ℓ, hℓ⟩ • (σ • x) + ℓ • x = 0

def DetFrobeniusMod (𝔪 : Ideal HeckeAlg) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p →
    ∀ A : ValuationSubring L, A.LiesOverPrime ℓ →
      ∀ σ : L ≃ₐ[K] L, A.IsFrobeniusAt σ ℓ →
        LinearMap.det (mTorsionGaloisRep J 𝔪 σ) = ((ℓ : HeckeAlg ⧸ 𝔪))

end LocalClauses

section MultiplicityOne

variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]

structure MultiplicityOneData (𝔪 : Ideal HeckeAlg) : Prop where
  isMaximal : 𝔪.IsMaximal
  resChar : (p : HeckeAlg) ∈ 𝔪
  finrank_two : Module.finrank (HeckeAlg ⧸ 𝔪) (heckeTorsion J 𝔪) = 2

end MultiplicityOne

def eisensteinSystem (N : ℕ) : Nat.Primes → ℤ :=
  fun ℓ => if (ℓ : ℕ) ∣ N then 1 else 1 + (ℓ : ℕ)

@[simp] lemma eisensteinSystem_of_not_dvd {N : ℕ} {ℓ : Nat.Primes} (h : ¬ (ℓ : ℕ) ∣ N) :
    eisensteinSystem N ℓ = 1 + (ℓ : ℕ) := if_neg h

@[simp] lemma eisensteinSystem_of_dvd {N : ℕ} {ℓ : Nat.Primes} (h : (ℓ : ℕ) ∣ N) :
    eisensteinSystem N ℓ = 1 := if_pos h

def eisensteinIdeal (N : ℕ) : Ideal HeckeAlg :=
  eigenIdeal (eisensteinSystem N)

section Support

variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]

def EigenformSupport (IsEig : Ideal HeckeAlg → Prop) : Prop :=
  ∀ 𝔪 : Ideal HeckeAlg, IsEig 𝔪 → ((p : HeckeAlg)) ∈ 𝔪 → MTorsionNeBot HeckeAlg J 𝔪

end Support

section Bundle

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) HeckeAlg J]

structure EichlerShimuraDataReduced (IsEig : Ideal HeckeAlg → Prop) : Prop where
  unramifiedOutside : UnramifiedOutside (K := K) (L := L) N p J
  frobeniusQuadratic : FrobeniusQuadratic (K := K) (L := L) N p J
  eigenformSupport : EigenformSupport p J IsEig

end Bundle

section Datum

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) HeckeAlg J]
variable (J' : Type*) [AddCommGroup J'] [Module HeckeAlg J']

structure IsSpecialization (A : ValuationSubring L) (ℓ : ℕ) (sp : J →+ J') (F : J' →+ J') :
    Prop where

  hecke_comm : ∀ (T : HeckeAlg) (x : J), sp (T • x) = T • sp x

  inertia_comm : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ x : J, sp (σ • x) = sp x

  frobenius_comm : ∀ σ : L ≃ₐ[K] L, A.IsFrobeniusAt σ ℓ → ∀ x : J, sp (σ • x) = F (sp x)

  injective_torsion : ∀ x : J, (∃ n : ℕ, p ^ n • x = 0) → sp x = 0 → x = 0

def SpecialFibreRelation (ℓ : ℕ) (hℓ : ℓ.Prime) (F : J' →+ J') : Prop :=
  ∀ y : J', F (F y) - heckeGen ⟨ℓ, hℓ⟩ • F y + ℓ • y = 0

end Datum

section Citation

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) HeckeAlg J]

def SpecializationExists : Prop :=
  ∀ ℓ : ℕ, (hℓ : ℓ.Prime) → ¬ ℓ ∣ N * p →
    ∀ A : ValuationSubring L, A.LiesOverPrime ℓ →
      ∃ (J' : Type) (_ : AddCommGroup J') (_ : Module HeckeAlg J') (sp : J →+ J')
        (F : J' →+ J'),
        IsSpecialization (K := K) p J J' A ℓ sp F ∧ SpecialFibreRelation J' ℓ hℓ F

end Citation

end ModularCurve
