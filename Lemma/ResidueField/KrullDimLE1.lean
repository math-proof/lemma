import Mathlib
import sympy.Basic
import Lemma.AlgebraicCurve.RegularProlongation
import Lemma.Int.P2MUtil

open AlgebraicCurve IsLocalRing

/--
[AlgebraicCurve_RegularProlongation_krullDimLE_one_integers](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_RegularProlongation_krullDimLE_one_integers.lean)
-/
@[path]
private lemma main
  [Field L] [Field F] [Algebra L F] [Field Fbar]
  {A : ValuationSubring L} [Ring.KrullDimLE 1 ↥A] [Algebra (ResidueField A) Fbar]
  {R : RegularProlongation A F Fbar} :
-- imply
  Ring.KrullDimLE 1 ↥R.integers := by
-- proof
  classical
  let O := R.integers
  let ι : ↥A →+* ↥O := (algebraMap L F).restrict A.toSubring O.toSubring fun a ha => (R.algebraMap_mem_iff a).mpr ha

  have key : ∀ f : ↥O, (f : F) ≠ 0 → ∃ (a : ↥A) (u : ↥O), IsUnit u ∧ f = ι a * u := by
    intro f hf0
    obtain ⟨c, hc, hres⟩ := R.exists_smul_mem (f : F) hf0
    have hu : IsUnit (⟨c • (f : F), hc⟩ : ↥O) := R.isUnit_of_residue_ne_zero hres
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hres
      have : (⟨(0 : L) • (f : F), hc⟩ : ↥O) = 0 := Subtype.ext (zero_smul _ _)
      rw [this, map_zero]
    have hcf0 : c • (f : F) ≠ 0 := smul_ne_zero hc0 hf0

    have hinvmem : (c • (f : F))⁻¹ ∈ O := by
      have h1 : ((hu.unit⁻¹ : (↥O)ˣ) : ↥O) * ⟨c • (f : F), hc⟩ = 1 := by
        have := hu.unit.inv_mul; rwa [IsUnit.unit_spec] at this
      have h2 := congrArg (fun z : ↥O => (z : F)) h1
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h2
      have h3 : (((hu.unit⁻¹ : (↥O)ˣ) : ↥O) : F) = (c • (f : F))⁻¹ := eq_inv_of_mul_eq_one_left h2
      rw [← h3]; exact ((hu.unit⁻¹ : (↥O)ˣ) : ↥O).2
    have hcinv_eq : algebraMap L F c⁻¹ = (f : F) * (c • (f : F))⁻¹ := by
      rw [Algebra.smul_def, mul_inv, map_inv₀]
      field_simp
    have hcinvO : algebraMap L F c⁻¹ ∈ O := by rw [hcinv_eq]; exact mul_mem f.2 hinvmem
    have hcinvA : c⁻¹ ∈ A := (R.algebraMap_mem_iff _).mp hcinvO
    refine ⟨⟨c⁻¹, hcinvA⟩, ⟨c • (f : F), hc⟩, hu, Subtype.ext ?_⟩
    change (f : F) = algebraMap L F c⁻¹ * (c • (f : F))
    rw [hcinv_eq, mul_assoc, inv_mul_cancel₀ hcf0, mul_one]

  refine Ring.KrullDimLE.mk₁' fun P hP0 hP => ?_
  have hne : Ideal.comap ι P ≠ ⊥ := by
    obtain ⟨f, hfP, hf0⟩ := P.ne_bot_iff.mp hP0
    have hf0' : (f : F) ≠ 0 := fun h => hf0 (Subtype.ext h)
    obtain ⟨a, u, hu, hf⟩ := key f hf0'
    intro hbot
    have haP : a ∈ Ideal.comap ι P := by
      rw [Ideal.mem_comap]
      rw [hf] at hfP
      exact (hP.mem_or_mem hfP).resolve_right fun h => hP.ne_top (Ideal.eq_top_of_isUnit_mem P h hu)
    rw [hbot, Ideal.mem_bot] at haP
    apply hf0
    rw [hf, haP, map_zero, zero_mul]
  haveI : (Ideal.comap ι P).IsPrime := Ideal.comap_isPrime ι P
  have hPA : Ideal.comap ι P = IsLocalRing.maximalIdeal ↥A :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal_of_ne_bot inferInstance hne)
  have hge : IsLocalRing.maximalIdeal ↥O ≤ P := by
    intro g hg
    by_cases hg0 : (g : F) = 0
    · have : g = 0 := Subtype.ext hg0
      rw [this]; exact P.zero_mem
    obtain ⟨a, u, hu, hgau⟩ := key g hg0
    have ha : ¬ IsUnit a := by
      intro hau
      apply (IsLocalRing.mem_maximalIdeal _).mp hg
      rw [hgau]; exact (hau.map ι).mul hu
    have haP : ι a ∈ P := by
      have : a ∈ Ideal.comap ι P := by rw [hPA]; exact (IsLocalRing.mem_maximalIdeal _).mpr ha
      exact this
    rw [hgau]; exact P.mul_mem_right _ haP
  have hPeq : P = IsLocalRing.maximalIdeal ↥O := le_antisymm (IsLocalRing.le_maximalIdeal hP.ne_top) hge
  rw [hPeq]; exact IsLocalRing.maximalIdeal.isMaximal ↥O


-- created on 2026-10-23
