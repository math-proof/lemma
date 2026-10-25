import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.RiemannTheorem
open RiemannRochSpace
open CurveWithOrd CurveDivisor


namespace RiemannRochSpace

/--
[riemann_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannTheorem.lean)
-/
@[path]
lemma riemann_inequality
  {D : CurveDivisor C} :
-- imply
  0 ≤ indexOfSpeciality (F := F) (k := k) D :=
-- proof
  indexOfSpeciality_nonneg D

end RiemannRochSpace

namespace RiemannRochSpace

/--
[effective_of_mem_riemannRochSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannTheorem.lean)
-/
@[path]
lemma effective_of_mem_riemannRochSpace
  {D : CurveDivisor C}
  {f : Fˣ}
-- given
  (hf : (f : F) ∈ riemannRochSpace (k := k) D) :
-- imply
  (principalDivisor f + D).IsEffective := by
-- proof
  rw [mem_riemannRochSpace_iff] at hf
  obtain (h0 | ⟨hne, heff⟩) := hf
  · exact absurd h0 f.ne_zero
  · convert heff using 2
    congr 1
    exact Units.ext rfl

end RiemannRochSpace

namespace RiemannRochSpace

/--
[exists_nonzero_of_divisorDim_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannTheorem.lean)
-/
@[path]
lemma exists_nonzero_of_divisorDim_pos
  {D : CurveDivisor C}
-- given
  (h : 1 ≤ divisorDim (F := F) (k := k) D) :
-- imply
  ∃ f : Fˣ, (f : F) ∈ riemannRochSpace (k := k) D := by
-- proof
  rw [divisorDim_eq_finrank] at h
  haveI : FiniteDimensional k (riemannRochSpace (F := F) (k := k) D) :=
    riemannRochSpace_finiteDimensional D
  have hpos : 0 < Module.finrank k (riemannRochSpace (F := F) (k := k) D) := by omega
  obtain ⟨⟨v, hv⟩, ⟨⟨w, hw⟩, hne⟩⟩ := Module.finrank_pos_iff.mp hpos
  by_cases h0 : v = 0
  · have hne' : w ≠ 0 := by
    intro hw0
    exact hne (Subtype.ext (h0.trans hw0.symm))
    exact ⟨Units.mk0 w hne', hw⟩
  · exact ⟨Units.mk0 v h0, hv⟩

end RiemannRochSpace

namespace RiemannRochSpace

/--
[indexOfSpeciality_eq_of_linearlyEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannTheorem.lean)
-/
@[path]
lemma indexOfSpeciality_eq_of_linearlyEquivalent
  {A B : CurveDivisor C}
-- given
  (h : PicardGroup.LinearlyEquivalent (CurveDivisor C) (principalDivisors (F := F)) A B) :
-- imply
  indexOfSpeciality (F := F) (k := k) A = indexOfSpeciality (F := F) (k := k) B := by
-- proof
  obtain ⟨f, hf⟩ := h
  simp only at hf
  have hdeg : degree C A = degree C B := by
    have hpd := degree_principalDivisor (C := C) (F := F) (k := k) f
    have : degree C (principalDivisor f) = degree C A - degree C B := by
      rw [hf, map_sub]
    linarith
  have hdim := divisorDim_eq_of_linearlyEquivalent (F := F) (k := k) A B ⟨f, hf⟩
  unfold indexOfSpeciality
  rw [hdeg, hdim]

end RiemannRochSpace

namespace RiemannRochSpace

/--
[riemann_equality_large_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannTheorem.lean)
-/
@[path]
lemma riemann_equality_large_degree
-- imply
  ∃ c : ℤ, ∀ D : CurveDivisor C, degree C D ≥ c → indexOfSpeciality (F := F) (k := k) D = 0 := by
-- proof
  classical
  obtain ⟨A, hA⟩ := genus_eq_degDim_of_max (C := C) (F := F) (k := k)
  have hiA : indexOfSpeciality (F := F) (k := k) A = 0 := by
    unfold indexOfSpeciality; linarith
  set g := genus (C := C) (F := F) (k := k) with g_def
  have hℓA : (divisorDim (F := F) (k := k) A : ℤ) = degree C A + 1 - (g : ℤ) := by linarith
  refine ⟨degree C A + (g : ℤ), fun D hD => ?_⟩
  have hdeg_sub : degree C (D - A) = degree C D - degree C A := map_sub (degree C) D A
  have hbound_DA := genus_bound (F := F) (k := k) (D - A)
  have hℓ_DA_pos : 1 ≤ divisorDim (F := F) (k := k) (D - A) := by omega
  obtain ⟨f, hf_mem⟩ := exists_nonzero_of_divisorDim_pos (D - A) hℓ_DA_pos
  have heff := effective_of_mem_riemannRochSpace (D - A) f hf_mem
  have hDprime_ge_A : A ≤ D + principalDivisor f := by
    rw [CurveDivisor.IsEffective] at heff
    intro P
    have hP := heff P
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply] at hP ⊢
    linarith
  haveI := riemannRochSpace_finiteDimensional (F := F) (k := k) A
  have ⟨hfd_Dprime, hbound_Dprime⟩ :=
    riemannRochSpace_finrank_le_of_le (F := F) (k := k) hDprime_ge_A
  have hdeg_Dprime : degree C (D + principalDivisor f) = degree C D := by
    rw [map_add, degree_principalDivisor, add_zero]
  have hi_Dprime : indexOfSpeciality (F := F) (k := k) (D + principalDivisor f) = 0 := by
    have h_nonneg := indexOfSpeciality_nonneg (F := F) (k := k) (D + principalDivisor f)
    rw [hdeg_Dprime] at hbound_Dprime
    rw [← divisorDim_eq_finrank, ← divisorDim_eq_finrank] at hbound_Dprime
    unfold indexOfSpeciality at h_nonneg ⊢
    rw [hdeg_Dprime] at h_nonneg
    have hg : (genus (C := C) (F := F) (k := k) : ℤ) = (g : ℤ) := by
      exact_mod_cast g_def.symm
    rw [hg] at h_nonneg ⊢
    linarith
  have hlinEquiv : PicardGroup.LinearlyEquivalent (CurveDivisor C)
    (principalDivisors (F := F)) D (D + principalDivisor f) := by
    refine ⟨f⁻¹, ?_⟩
    simp only [principalDivisor_inv]
    abel
  have hi_eq := indexOfSpeciality_eq_of_linearlyEquivalent D
    (D + principalDivisor f) hlinEquiv
  linarith

end RiemannRochSpace

namespace RiemannRochSpace

/--
[riemann_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannTheorem.lean)
-/
@[path]
lemma riemann_theorem
-- imply
  (∀ D : CurveDivisor C, 0 ≤ indexOfSpeciality (F := F) (k := k) D) ∧ (∃ c : ℤ, ∀ D : CurveDivisor C, degree C D ≥ c → indexOfSpeciality (F := F) (k := k) D = 0) :=
-- proof
  ⟨riemann_inequality, riemann_equality_large_degree⟩

end RiemannRochSpace


-- created on 2026-10-23
