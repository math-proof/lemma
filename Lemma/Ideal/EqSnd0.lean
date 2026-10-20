import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[Ideal_snd_apply_eq_zero_of_mem_minimalPrimes_of_isMaximal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_snd_apply_eq_zero_of_mem_minimalPrimes_of_isMaximal.lean)
-/
@[path]
private lemma main
    (L : Type) [Field L] [CharZero L] (R : Type) [CommRing R] [Algebra L R] [IsReduced R]
    (𝔭 : Ideal R) (h𝔭 : 𝔭 ∈ (⊥ : Ideal R).minimalPrimes) (h𝔭' : 𝔭.IsMaximal)
    [Module.Finite L (R ⧸ 𝔭)]
    (K : Type) [Field K] [Algebra L K]
    (φ : R →ₐ[L] DualNumber K)
    (hφ : RingHom.ker ((TrivSqZeroExt.fstHom L K K).comp φ).toRingHom = 𝔭) :
    ∀ r : R, (φ r).snd = 0 := by
  classical
  let h𝔭p : 𝔭.IsPrime := h𝔭.1.1
  have hfst : ∀ r : R, (φ r).fst = 0 ↔ r ∈ 𝔭 := by
    intro r
    rw [← hφ, RingHom.mem_ker]
    rfl
  have hkill : ∀ p ∈ 𝔭, φ p = 0 := by
    intro p hp
    have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := Localization.AtPrime 𝔭) 𝔭 ⊥ h𝔭
    have hmem : algebraMap R (Localization.AtPrime 𝔭) p ∈ (Ideal.map (algebraMap R (Localization.AtPrime 𝔭)) ⊥).radical := by
      rw [hrad]; exact Ideal.mem_map_of_mem _ hp
    rw [Ideal.map_bot] at hmem
    obtain ⟨n, hn⟩ := hmem
    rw [Ideal.mem_bot] at hn
    have hnil : IsNilpotent (algebraMap R (Localization.AtPrime 𝔭) p) := ⟨n, hn⟩
    have h0 : algebraMap R (Localization.AtPrime 𝔭) p = 0 := hnil.eq_zero
    obtain ⟨⟨s, hs⟩, hsp⟩ := (IsLocalization.map_eq_zero_iff 𝔭.primeCompl (Localization.AtPrime 𝔭) p).mp h0
    have hs' : (φ s).fst ≠ 0 := fun h => hs ((hfst s).mp h)
    have hprod : φ s * φ p = 0 := by rw [← map_mul, hsp, map_zero]
    have h1 : (φ p).fst = 0 := by
      have := congrArg TrivSqZeroExt.fst hprod
      rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hs'
    have h2 : (φ p).snd = 0 := by
      have := congrArg TrivSqZeroExt.snd hprod
      rw [DualNumber.snd_mul, h1, mul_zero, add_zero, TrivSqZeroExt.snd_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hs'
    exact TrivSqZeroExt.ext h1 h2
  let _ : 𝔭.IsMaximal := h𝔭'
  let _ : Field (R ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  let φ' : (R ⧸ 𝔭) →ₐ[L] DualNumber K := Ideal.Quotient.liftₐ 𝔭 φ hkill
  have hφ' : ∀ r : R, φ' (Ideal.Quotient.mk 𝔭 r) = φ r := fun r => rfl
  let _ : Algebra.IsIntegral L (R ⧸ 𝔭) := Algebra.IsIntegral.of_finite L (R ⧸ 𝔭)
  let _ : Algebra.IsSeparable L (R ⧸ 𝔭) := Algebra.IsSeparable.of_integral L (R ⧸ 𝔭)
  let _ : Algebra.FormallyUnramified L (R ⧸ 𝔭) := Algebra.FormallyUnramified.of_isSeparable L (R ⧸ 𝔭)
  let I : Ideal (DualNumber K) := TrivSqZeroExt.kerIdeal K K
  have hI : IsNilpotent I := ⟨2, TrivSqZeroExt.kerIdeal_sq K K⟩
  let g₂ : (R ⧸ 𝔭) →ₐ[L] DualNumber K :=
    (TrivSqZeroExt.inlAlgHom L K K).comp ((TrivSqZeroExt.fstHom L K K).comp φ')
  have hg₂ : ∀ x, g₂ x = TrivSqZeroExt.inl (φ' x).fst := fun x => rfl
  have heq : φ' = g₂ := by
    refine Algebra.FormallyUnramified.ext I hI (fun x => ?_)
    rw [Ideal.Quotient.eq, hg₂]
    show φ' x - TrivSqZeroExt.inl (φ' x).fst ∈ RingHom.ker (TrivSqZeroExt.fstHom K K K)
    rw [RingHom.mem_ker, map_sub]
    show (φ' x).fst - (TrivSqZeroExt.inl (φ' x).fst : DualNumber K).fst = 0
    rw [TrivSqZeroExt.fst_inl, sub_self]
  intro r
  rw [← hφ', heq, hg₂, TrivSqZeroExt.snd_inl]

-- created on 2026-10-20
