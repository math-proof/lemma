import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Lemma.Definitions.Def_FLTPrelim_FreyPackage
import Lemma.Definitions.Def_FLTPrelim_GaloisRep
import Lemma.Definitions.Def_FLTPrelim_Modularity

set_option autoImplicit false

noncomputable section

open WeierstrassCurve CuspForm

namespace FLTPrelim

lemma not_isUnit_natCast_integralClosure {p : ℕ} (hp : p.Prime) :
    ¬ IsUnit (p : integralClosure ℤ ℂ) := by
  intro h
  obtain ⟨u, hu⟩ := h

  set x : integralClosure ℤ ℂ := ((u⁻¹ : (integralClosure ℤ ℂ)ˣ) : integralClosure ℤ ℂ) with hx
  have h1 : (p : integralClosure ℤ ℂ) * x = 1 := by
    rw [hx, ← hu]; exact u.mul_inv

  have h2 : (p : ℂ) * (x : ℂ) = 1 := by
    have := congrArg (fun z : integralClosure ℤ ℂ => (z : ℂ)) h1
    push_cast at this; simpa using this
  have hpne : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero

  have hxval : (x : ℂ) = (p : ℂ)⁻¹ := by field_simp; linear_combination h2
  have hint : IsIntegral ℤ ((p : ℂ)⁻¹) := by rw [← hxval]; exact x.2

  have hmap : (algebraMap ℚ ℂ) ((p : ℚ)⁻¹) = (p : ℂ)⁻¹ := by
    rw [eq_ratCast (algebraMap ℚ ℂ)]; push_cast; rfl
  rw [← hmap] at hint
  have hintQ : IsIntegral ℤ ((p : ℚ)⁻¹) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp hint

  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintQ
  rw [eq_intCast] at hm
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmul : ((p * m : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
    push_cast; rw [hm]; field_simp
  have hdvd : (p : ℤ) ∣ 1 := ⟨m, (Int.cast_injective hmul).symm⟩
  have hple : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
  have := hp.two_le; omega

lemma exists_maximalIdeal_natCast_prime_mem {p : ℕ} (hp : p.Prime) :
    ∃ 𝔪 : Ideal (integralClosure ℤ ℂ), 𝔪.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪 := by
  have hne : Ideal.span {(p : integralClosure ℤ ℂ)} ≠ ⊤ := fun htop =>
    not_isUnit_natCast_integralClosure hp (Ideal.span_singleton_eq_top.mp htop)
  obtain ⟨𝔪, h𝔪max, h𝔪le⟩ := Ideal.exists_le_maximal _ hne
  exact ⟨𝔪, h𝔪max, h𝔪le (Ideal.subset_span rfl)⟩

end FLTPrelim

namespace FreyPackage

open FLTPrelim

def ModularRepOfLevel (P : FreyPackage) (N : ℕ) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (W : WeierstrassCurve ℤ)
      (𝔪 : Ideal (integralClosure ℤ ℂ)),
    f.IsNormalizedEigenform ∧ W.IsIntegralModelOf P.freyCurve ∧
    𝔪.IsMaximal ∧ (P.p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

end FreyPackage

namespace WeierstrassCurve

def IsResiduallyModularOfLevel (W : WeierstrassCurve ℤ) (p M : ℕ) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (𝔪 : Ideal (integralClosure ℤ ℂ)),
    f.IsNormalizedEigenform ∧ 𝔪.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

def IsResiduallyModular (W : WeierstrassCurve ℤ) (p : ℕ) : Prop :=
  ∃ M : ℕ, 0 < M ∧ W.IsResiduallyModularOfLevel p M

def IsModularModelOfConductorLevel (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ W.IsModularModelOfLevel N ∧
    ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ W.Δ → ℓ ∣ N

theorem IsModularModelOfConductorLevel.isModularModel {W : WeierstrassCurve ℤ}
    (h : W.IsModularModelOfConductorLevel) : W.IsModularModel := by
  obtain ⟨N, hN, hmod, -⟩ := h
  exact ⟨N, hN, hmod⟩

def ModRepIsIrreducible (W : WeierstrassCurve ℤ) (n : ℕ) : Prop :=
  Affine.Point.GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ
    (W.map (Int.castRingHom ℚ)) n

end WeierstrassCurve

namespace CuspForm

open ModularFormClass

open UpperHalfPlane in

theorem IsNormalizedEigenform.ne_zero {N : ℕ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) :
    f ≠ 0 := by
  rintro rfl
  have h0 : qCoeff (0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2) 1 = 0 := by
    have hcoe : ((0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : ℍ → ℂ) = (0 : ℍ → ℂ) := rfl
    rw [qCoeff, hcoe, qExpansion_zero]
    simp
  exact zero_ne_one (h0 ▸ hf.qCoeff_one)

end CuspForm

end
