import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.ScalingStep
open Polynomial IsLocalRing


/--
[primitive_exists_coeff_not_in_maxIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ScalingStep.lean)
-/
@[path]
lemma primitive_exists_coeff_not_in_maxIdeal
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {g : A[X]}
-- given
  (hprim : g.IsPrimitive) :
-- imply
  ∃ i, g.coeff i ∉ maximalIdeal A := by
-- proof
  by_contra hall
  push_neg at hall
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_prime A
  have hspan : maximalIdeal A = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ.irreducible
  have : C π ∣ g := by
    rw [C_dvd_iff_dvd_coeff]
    intro i; rw [hspan] at hall; exact Ideal.mem_span_singleton.mp (hall i)
  exact hπ.irreducible.1 ((isPrimitive_iff_isUnit_of_C_dvd.mp hprim) π this)

/--
[dvd_content_of_coeff_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ScalingStep.lean)
-/
@[path]
lemma dvd_content_of_coeff_unit
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {b : A}
  {f : K[X]}
  {j : ℕ}
  {a : A}
-- given
  (h : A[X])
  (hmap : map (algebraMap A K) h = C (algebraMap A K b) * f)
  (ha : algebraMap A K a = f.coeff j)
  (hu : IsUnit ((primPart h).coeff j)) :
-- imply
  b ∣ h.content := by
-- proof
  have hcoeff : h.coeff j = h.content * (h.primPart).coeff j := by
    conv_lhs => rw [eq_C_content_mul_primPart h]; simp only [coeff_C_mul]
  have hmapj : algebraMap A K (h.coeff j) = algebraMap A K (b * a) := by
    have := congr_arg (fun p => coeff p j) hmap
    simp only [coeff_map, coeff_C_mul, ← ha, ← map_mul] at this; exact this
  have heq : h.coeff j = b * a := IsFractionRing.injective A K hmapj
  have key : h.content * (h.primPart).coeff j = b * a := by rw [← hcoeff, heq]
  exact (IsUnit.dvd_mul_right hu).mp ⟨a, key⟩

/--
[f_in_image_of_dvd_content](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ScalingStep.lean)
-/
@[path]
lemma f_in_image_of_dvd_content
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {b : A}
  {f : K[X]}
-- given
  (h : A[X])
  (hb : b ≠ 0)
  (hmap : map (algebraMap A K) h = C (algebraMap A K b) * f)
  (hdvd : b ∣ h.content) :
-- imply
  ∃ g : A[X], f = map (algebraMap A K) g := by
-- proof
  obtain ⟨d, hd⟩ := hdvd
  have hb_ne : (algebraMap A K b) ≠ 0 :=
    fun heq => hb ((IsFractionRing.injective A K) (by rwa [map_zero]))
  use C d * h.primPart
  ext i
  simp only [coeff_map, coeff_C_mul, map_mul]
  have hmapj : algebraMap A K (h.coeff i) = algebraMap A K b * f.coeff i := by
    have := congr_arg (fun p => coeff p i) hmap
    simp only [coeff_map, coeff_C_mul] at this; exact this
  have hcoeff : h.coeff i = h.content * (h.primPart).coeff i := by
    conv_lhs => rw [eq_C_content_mul_primPart h]; simp only [coeff_C_mul]
  apply mul_left_cancel₀ hb_ne
  rw [← hmapj, hcoeff, hd, map_mul, map_mul]; ring

/--
[primPart_irred_of_map_irred](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ScalingStep.lean)
-/
@[path]
lemma primPart_irred_of_map_irred
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {b : A}
  {f : K[X]}
-- given
  (h : A[X])
  (hh : h ≠ 0)
  (hb : b ≠ 0)
  (hirr : Irreducible f)
  (hmap : map (algebraMap A K) h = C (algebraMap A K b) * f) :
-- imply
  Irreducible (primPart h) := by
-- proof
  apply IsPrimitive.irreducible_of_irreducible_map_of_injective (IsFractionRing.injective A K)
    h.isPrimitive_primPart
  have hcne : algebraMap A K h.content ≠ 0 :=
    fun heq => hh (content_eq_zero_iff.mp ((IsFractionRing.injective A K) (by rwa [map_zero])))
  have h_decomp : map (algebraMap A K) h =
    C (algebraMap A K h.content) * map (algebraMap A K) (h.primPart) := by
    conv_lhs => rw [eq_C_content_mul_primPart h, Polynomial.map_mul, Polynomial.map_C]
  have key : map (algebraMap A K) (h.primPart) =
    C ((algebraMap A K h.content)⁻¹ * algebraMap A K b) * f := by
    have h1 : C (algebraMap A K h.content) * map (algebraMap A K) (h.primPart) =
      C (algebraMap A K b) * f := h_decomp.symm ▸ hmap
    have h2 := congr_arg (C (algebraMap A K h.content)⁻¹ * ·) h1
    simp only [← mul_assoc, ← C_mul, inv_mul_cancel₀ hcne, C_1, one_mul] at h2
    exact h2
  rw [key]
  exact (irreducible_isUnit_mul (isUnit_C.mpr (Ne.isUnit (mul_ne_zero
    (inv_ne_zero hcne)
    (fun heq => hb ((IsFractionRing.injective A K) (by rwa [map_zero]))))))).mpr hirr
section ScalingStepMain
variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/--
[coeff_in_maxIdeal_of_not_inA](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ScalingStep.lean)
-/
@[path]
lemma coeff_in_maxIdeal_of_not_inA
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {b : A}
  {f : K[X]}
  {j : ℕ}
  {a : A}
-- given
  (h : A[X])
  (hb : b ≠ 0)
  (hmap : map (algebraMap A K) h = C (algebraMap A K b) * f)
  (hnotinA : ¬∃ g : A[X], f = Polynomial.map (algebraMap A K) g)
  (ha : algebraMap A K a = f.coeff j) :
-- imply
  (primPart h).coeff j ∈ maximalIdeal A := by
-- proof
  rw [mem_maximalIdeal]
  intro hu
  exact hnotinA (f_in_image_of_dvd_content h b hb f hmap (dvd_content_of_coeff_unit h b f hmap j a ha hu))

/--
[natDegree_primPart_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ScalingStep.lean)
-/
@[path]
lemma natDegree_primPart_eq
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {b : A}
  {f : K[X]}
-- given
  (h : A[X])
  (hh : h ≠ 0)
  (hb : b ≠ 0)
  (hmap : map (algebraMap A K) h = C (algebraMap A K b) * f) :
-- imply
  (primPart h).natDegree = f.natDegree := by
-- proof
  have hbK : (algebraMap A K b) ≠ 0 :=
    fun heq => hb ((IsFractionRing.injective A K) (by rwa [map_zero]))
  have hcne : h.content ≠ 0 := fun h_eq => hh (content_eq_zero_iff.mp h_eq)
  have hd1 : h.natDegree = f.natDegree := by
    have := natDegree_map_eq_of_injective (IsFractionRing.injective A K) h
    rw [hmap, natDegree_C_mul hbK] at this; exact this.symm
  have hd2 : h.natDegree = (primPart h).natDegree := by
    conv_lhs => rw [eq_C_content_mul_primPart h]; exact natDegree_C_mul hcne
  linarith
set_option maxHeartbeats 300000 in

/--
[hensel_kurschak_scaling_step'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ScalingStep.lean)
-/
@[path]
lemma hensel_kurschak_scaling_step'
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {f : K[X]}
-- given
  (hirr : Irreducible f)
  (hlead : ∃ a : A, algebraMap A K a = f.leadingCoeff)
  (hconst : ∃ a : A, algebraMap A K a = f.coeff 0)
  (hnotinA : ¬∃ g : A[X], f = Polynomial.map (algebraMap A K) g) :
-- imply
  ∃ (g : A[X]), Irreducible g ∧ g.coeff 0 ∈ maximalIdeal A ∧ g.coeff g.natDegree ∈ maximalIdeal A ∧ (∃ i, ¬(g.coeff i ∈ maximalIdeal A)) := by
-- proof
  set h := IsLocalization.integerNormalization (nonZeroDivisors A) f with hh_def
  obtain ⟨b, hb_mem, hb_eq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) f
  have hb_ne : b ≠ 0 := nonZeroDivisors.ne_zero hb_mem
  have hmap : map (algebraMap A K) h = C (algebraMap A K b) * f := by
    rw [hb_eq]; ext i; simp [coeff_C_mul, Algebra.smul_def]
  have hne : h ≠ 0 := by
    intro heq
    have hbK : (algebraMap A K b) ≠ 0 :=
      fun h => hb_ne ((IsFractionRing.injective A K) (by rwa [map_zero]))
    have : (0 : K[X]) = C (algebraMap A K b) * f := by rw [← hmap, heq, Polynomial.map_zero]
    exact hirr.ne_zero ((mul_eq_zero.mp this.symm).resolve_left (by simp [hbK]))
  set g := h.primPart
  obtain ⟨a₀, ha₀⟩ := hconst
  obtain ⟨aₙ, haₙ⟩ := hlead
  have hirr_g : Irreducible g := primPart_irred_of_map_irred h hne b hb_ne f hirr hmap
  have hprim_coeff : ∃ i, g.coeff i ∉ maximalIdeal A :=
    primitive_exists_coeff_not_in_maxIdeal g h.isPrimitive_primPart
  have hconst_mem : g.coeff 0 ∈ maximalIdeal A :=
    coeff_in_maxIdeal_of_not_inA h b hb_ne f hmap hnotinA 0 a₀ ha₀
  have hdeg : g.natDegree = f.natDegree :=
    natDegree_primPart_eq h hne b hb_ne f hmap
  have hlead_mem : g.coeff g.natDegree ∈ maximalIdeal A := by
    rw [hdeg]
    exact coeff_in_maxIdeal_of_not_inA h b hb_ne f hmap hnotinA f.natDegree aₙ haₙ
  exact ⟨g, hirr_g, hconst_mem, hlead_mem, hprim_coeff⟩
end ScalingStepMain


-- created on 2026-10-23
