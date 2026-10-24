import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Discriminant
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell.CubicInduction

def IsAnisotropicAt (a b : ℚ) (p : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  ¬ ∃ z x y : p.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
    z ^ 2 - algebraMap ℚ (p.adicCompletion ℚ) a * x ^ 2
      - algebraMap ℚ (p.adicCompletion ℚ) b * y ^ 2 = 0

variable (K : Type) [Field K] [NumberField K]

noncomputable def discQ : ℚ := Algebra.discr ℚ (Module.finBasis ℚ K)

theorem discQ_ne_zero : discQ K ≠ 0 := Algebra.discr_not_zero_of_basis ℚ (Module.finBasis ℚ K)

open scoped Classical in

noncomputable def lamSq (p : HeightOneSpectrum (𝓞 ℚ)) : ℂ :=
  if IsAnisotropicAt (discQ K) (-1) p then -1 else 1

noncomputable def lamSqArch : ℂ := if discQ K < 0 then -1 else 1

theorem lamSq_eq_one_or_eq_neg_one (p : HeightOneSpectrum (𝓞 ℚ)) :
    lamSq K p = 1 ∨ lamSq K p = -1 := by
  unfold lamSq
  split_ifs <;> simp

theorem lamSqArch_eq_one_or_eq_neg_one : lamSqArch K = 1 ∨ lamSqArch K = -1 := by
  unfold lamSqArch
  split_ifs <;> simp

section Rescaling

theorem isAnisotropicAt_mul_sq_left_iff {a b c : ℚ} (hc : c ≠ 0) (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsAnisotropicAt (c ^ 2 * a) b p ↔ IsAnisotropicAt a b p := by
  unfold IsAnisotropicAt
  have hc' : algebraMap ℚ (p.adicCompletion ℚ) c ≠ 0 :=
    (map_ne_zero (algebraMap ℚ (p.adicCompletion ℚ))).mpr hc
  constructor
  · intro h ⟨z, x, y, hne, hzxy⟩
    refine h ⟨z, x / algebraMap ℚ (p.adicCompletion ℚ) c, y, ?_, ?_⟩
    · rintro ⟨hz, hx, hy⟩
      exact hne ⟨hz, (div_eq_zero_iff.mp hx).resolve_right hc', hy⟩
    · rw [map_mul, map_pow, div_pow, ← hzxy]
      field_simp
  · intro h ⟨z, x, y, hne, hzxy⟩
    refine h ⟨z, algebraMap ℚ (p.adicCompletion ℚ) c * x, y, ?_, ?_⟩
    · rintro ⟨hz, hx, hy⟩
      exact hne ⟨hz, (mul_eq_zero.mp hx).resolve_left hc', hy⟩
    · rw [map_mul, map_pow] at hzxy
      rw [← hzxy, mul_pow]
      ring

end Rescaling

section BasisIndependence

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_discr_eq_sq_mul_discQ (b : Module.Basis ι ℚ K) :
    ∃ c : ℚ, c ≠ 0 ∧ Algebra.discr ℚ ⇑b = c ^ 2 * discQ K := by
  have hcard : Fintype.card (Fin (Module.finrank ℚ K)) = Fintype.card ι := by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis b]
  let e : Module.Basis ι ℚ K := (Module.finBasis ℚ K).reindex (Fintype.equivOfCardEq hcard)
  have he : Algebra.discr ℚ ⇑e = discQ K := by
    rw [discQ, Module.Basis.coe_reindex]
    exact Algebra.discr_reindex ℚ (Module.finBasis ℚ K) (Fintype.equivOfCardEq hcard)
  have hb : (⇑b : ι → K) = Matrix.vecMul ⇑e ((e.toMatrix ⇑b).map ⇑(algebraMap ℚ K)) := by
    funext j
    rw [← e.sum_toMatrix_smul_self ⇑b j]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Algebra.smul_def]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hd : Algebra.discr ℚ ⇑b = (e.toMatrix ⇑b).det ^ 2 * discQ K := by
    conv_lhs => rw [hb]
    rw [Algebra.discr_of_matrix_vecMul, he]
  exact ⟨(e.toMatrix ⇑b).det, (e.isUnit_det b).ne_zero, hd⟩

theorem isAnisotropicAt_discr_iff (b : Module.Basis ι ℚ K) (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsAnisotropicAt (Algebra.discr ℚ ⇑b) (-1) p ↔ IsAnisotropicAt (discQ K) (-1) p := by
  obtain ⟨c, hc, hcb⟩ := exists_discr_eq_sq_mul_discQ K b
  rw [hcb]
  exact isAnisotropicAt_mul_sq_left_iff hc p

theorem discr_neg_iff (b : Module.Basis ι ℚ K) : Algebra.discr ℚ ⇑b < 0 ↔ discQ K < 0 := by
  obtain ⟨c, hc, hcb⟩ := exists_discr_eq_sq_mul_discQ K b
  have hc2 : 0 < c ^ 2 := by positivity
  rw [hcb, mul_neg_iff]
  simp [hc2, not_lt.mpr hc2.le]

end BasisIndependence

section PlacesOfK

variable [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

noncomputable def lamSqFin (w : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal = 1 ∧
      (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal = 1 then 1
  else lamSq K (w.under (𝓞 ℚ))

end PlacesOfK

end LanglandsTunnell.CubicInduction
