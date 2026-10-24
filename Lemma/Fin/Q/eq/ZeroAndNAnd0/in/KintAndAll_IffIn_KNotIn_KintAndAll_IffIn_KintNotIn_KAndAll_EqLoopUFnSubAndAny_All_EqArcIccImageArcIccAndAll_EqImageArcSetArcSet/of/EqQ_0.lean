import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_CellDissection
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open Int
open AlgebraicCurve Set
open scoped Real


/--
[AlgebraicCurve_RadialRegion_exists_recip](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_recip.lean)
-/
private noncomputable def recip
  (R : RadialRegion)
  : RadialRegion where
  q := 0
  r := (fun φ => (R.r (-φ))⁻¹)
  hcont := ((R.hcont.comp continuous_neg).inv₀ fun φ => (R.hpos _).ne')
  hper := by
    intro φ
    show (R.r (-(φ + 2 * Real.pi)))⁻¹ = (R.r (-φ))⁻¹
    congr 1
    have h1 : -(φ + 2 * Real.pi) = -φ - 2 * Real.pi := by ring
    rw [h1, R.hper.sub_eq]
  hpos := (fun φ => inv_pos.mpr (R.hpos _))
  N := R.N
  φs := (fun k => 2 * Real.pi - R.φs (Fin.rev k))
  hφ0 := by
    show 2 * Real.pi - R.φs (Fin.rev 0) = 0
    rw [Fin.rev_zero, R.hφN]
    ring
  hφN := by
    show 2 * Real.pi - R.φs (Fin.rev (Fin.last R.N)) = 2 * Real.pi
    rw [Fin.rev_last, R.hφ0]
    ring
  hmono := by
    intro k l hkl
    have h1 : Fin.rev l < Fin.rev k := by
      rw [Fin.lt_def, Fin.val_rev, Fin.val_rev]
      rw [Fin.lt_def] at hkl
      omega
    have h2 := R.hmono h1
    show 2 * Real.pi - R.φs (Fin.rev k) < 2 * Real.pi - R.φs (Fin.rev l)
    linarith
  hC2 := by
    intro k'
    have hicc : Set.Icc (2 * Real.pi - R.φs (Fin.rev k'.castSucc))
      (2 * Real.pi - R.φs (Fin.rev k'.succ)) =
      Set.Icc (2 * Real.pi - R.φs ((Fin.rev k').succ))
        (2 * Real.pi - R.φs ((Fin.rev k').castSucc)) := by
      rw [Fin.rev_castSucc, Fin.rev_succ]
    show ContDiffOn ℝ 2 (fun φ => (R.r (-φ))⁻¹)
      (Set.Icc (2 * Real.pi - R.φs (Fin.rev k'.castSucc))
        (2 * Real.pi - R.φs (Fin.rev k'.succ)))
    rw [hicc]
    have hmaps : Set.MapsTo (fun φ => 2 * Real.pi - φ)
        (Set.Icc (2 * Real.pi - R.φs ((Fin.rev k').succ))
          (2 * Real.pi - R.φs ((Fin.rev k').castSucc)))
        (Set.Icc (R.φs ((Fin.rev k').castSucc)) (R.φs ((Fin.rev k').succ))) := by
      intro φ hφ
      obtain ⟨h1, h2⟩ := hφ
      exact ⟨by linarith, by linarith⟩
    have h1 : ContDiffOn ℝ 2 (fun φ => R.r (2 * Real.pi - φ))
        (Set.Icc (2 * Real.pi - R.φs ((Fin.rev k').succ))
          (2 * Real.pi - R.φs ((Fin.rev k').castSucc))) :=
      (R.hC2 (Fin.rev k')).comp ((contDiff_const.sub contDiff_id).contDiffOn) hmaps
    have h2 : ContDiffOn ℝ 2 (fun φ => (R.r (2 * Real.pi - φ))⁻¹)
        (Set.Icc (2 * Real.pi - R.φs ((Fin.rev k').succ))
          (2 * Real.pi - R.φs ((Fin.rev k').castSucc))) :=
      h1.inv fun φ _ => (R.hpos _).ne'
    refine h2.congr ?_
    intro φ _
    show (R.r (-φ))⁻¹ = (R.r (2 * Real.pi - φ))⁻¹
    congr 1
    have h3 : -φ = (2 * Real.pi - φ) - 2 * Real.pi := by ring
    rw [h3, R.hper.sub_eq]

private def idx
  (R : RadialRegion)
  (k : Fin R.N) : Fin (recip R).N := k

private def unidx
  (R : RadialRegion)
  (k : Fin (recip R).N) : Fin R.N := k

private def arcEquiv
  (R : RadialRegion)
  : Fin R.N ≃ Fin (recip R).N where
  toFun k := idx R (Fin.rev k)
  invFun j := Fin.rev (unidx R j)
  left_inv k := by
    show Fin.rev (Fin.rev k) = k
    exact Fin.rev_rev k
  right_inv j := by
    show Fin.rev (Fin.rev (unidx R j)) = unidx R j
    exact Fin.rev_rev _

private lemma le_inv_flip {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ≤ b⁻¹) :
  b ≤ a⁻¹ := by
  have h1 : a * b ≤ 1 := calc
    _ ≤ b⁻¹ * b := mul_le_mul_of_nonneg_right h hb.le
    _ = 1 := inv_mul_cancel₀ hb.ne'
  calc
    _ = a⁻¹ * (a * b) := by field_simp
    _ ≤ a⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr ha).le
    _ = a⁻¹ := mul_one _

private lemma lt_inv_flip {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a < b⁻¹) :
  b < a⁻¹ := by
  by_contra hcon
  push Not at hcon
  have h1 : b⁻¹ ≤ a⁻¹⁻¹ :=
    le_inv_flip (inv_pos.mpr ha) (inv_pos.mpr hb) (by rwa [inv_inv])
  rw [inv_inv] at h1
  exact absurd (lt_of_lt_of_le h h1) (lt_irrefl a)

private lemma r_arg_inv
  (R : RadialRegion)
  (w : ℂ) : R.r (Complex.arg w⁻¹) = R.r (-Complex.arg w) := by
  rw [Complex.arg_inv]
  split_ifs with h
  ·
    rw [h]
    have h1 := R.hper (-Real.pi)
    have h2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [h2] at h1
    rw [← h1]
  · rfl

private lemma loop_periodic
  (R : RadialRegion)
  (φ : ℝ) : R.loop (φ + 2 * Real.pi) = R.loop φ := by
  show R.q + (R.r (φ + 2 * Real.pi) : ℂ) *
      Complex.exp (((φ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
    R.q + (R.r φ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
  rw [R.hper φ]
  have h : (((φ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
      (φ : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

private lemma loop_two_pi_sub
  (R : RadialRegion)
  (x : ℝ) : R.loop (2 * Real.pi - x) = R.loop (-x) := by
  have h := loop_periodic R (-x)
  rwa [show -x + 2 * Real.pi = 2 * Real.pi - x by ring] at h

private lemma recip_q
  (R : RadialRegion)
  : (recip R).q = 0 := rfl

private lemma recip_N
  (R : RadialRegion)
  : (recip R).N = R.N := rfl

private lemma loop_recip
  (R : RadialRegion)
  (hq : R.q = 0) (φ : ℝ) : ((recip R).loop φ)⁻¹ = R.loop (-φ) := by
  show ((0 : ℂ) + (((R.r (-φ))⁻¹ : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))⁻¹ =
    R.q + (R.r (-φ) : ℂ) * Complex.exp (((-φ : ℝ) : ℂ) * Complex.I)
  rw [hq]
  simp only [zero_add, Complex.ofReal_inv, Complex.ofReal_neg, neg_mul, Complex.exp_neg, mul_inv,
    inv_inv]

private lemma loop_recip_eq
  (R : RadialRegion)
  (hq : R.q = 0) (θ : ℝ) :
  (recip R).loop θ = (R.loop (2 * Real.pi - θ))⁻¹ := by
  rw [loop_two_pi_sub R θ, ← loop_recip R hq θ, inv_inv]

private lemma zero_mem_Kint
  (R : RadialRegion)
  : (0 : ℂ) ∈ (recip R).Kint := by
  show ‖(0 : ℂ) - 0‖ < (R.r (-Complex.arg ((0 : ℂ) - 0)))⁻¹
  rw [sub_zero, norm_zero]
  exact inv_pos.mpr (R.hpos _)

private lemma mem_K_iff
  (R : RadialRegion)
  (hq : R.q = 0) {w : ℂ} (hw : w ≠ 0) : w ∈ (recip R).K ↔ w⁻¹ ∉ R.Kint := by
  have hK : w ∈ (recip R).K ↔ ‖w‖ ≤ (R.r (-Complex.arg w))⁻¹ := by
    show ‖w - 0‖ ≤ (R.r (-Complex.arg (w - 0)))⁻¹ ↔ _
    rw [sub_zero]
  have hKint : w⁻¹ ∉ R.Kint ↔ R.r (-Complex.arg w) ≤ ‖w‖⁻¹ := by
    show ¬(‖w⁻¹ - R.q‖ < R.r (Complex.arg (w⁻¹ - R.q))) ↔ _
    rw [hq, sub_zero, not_lt, r_arg_inv R w, norm_inv]
  rw [hK, hKint]
  constructor
  ·
    intro h
    exact le_inv_flip (norm_pos_iff.mpr hw) (R.hpos _) h
  ·
    intro h
    exact le_inv_flip (R.hpos _) (norm_pos_iff.mpr hw) h

private lemma mem_Kint_iff
  (R : RadialRegion)
  (hq : R.q = 0) {w : ℂ} (hw : w ≠ 0) :
  w ∈ (recip R).Kint ↔ w⁻¹ ∉ R.K := by
  have hKint : w ∈ (recip R).Kint ↔ ‖w‖ < (R.r (-Complex.arg w))⁻¹ := by
    show ‖w - 0‖ < (R.r (-Complex.arg (w - 0)))⁻¹ ↔ _
    rw [sub_zero]
  have hK : w⁻¹ ∉ R.K ↔ R.r (-Complex.arg w) < ‖w‖⁻¹ := by
    show ¬(‖w⁻¹ - R.q‖ ≤ R.r (Complex.arg (w⁻¹ - R.q))) ↔ _
    rw [hq, sub_zero, not_le, r_arg_inv R w, norm_inv]
  rw [hKint, hK]
  constructor
  ·
    intro h
    exact lt_inv_flip (norm_pos_iff.mpr hw) (R.hpos _) h
  ·
    intro h
    exact lt_inv_flip (R.hpos _) (norm_pos_iff.mpr hw) h

private lemma image_inv_arcSet
  (R : RadialRegion)
  (hq : R.q = 0) (k : Fin R.N) :
  (fun w : ℂ => w⁻¹) '' (recip R).arcSet (idx R (Fin.rev k)) = R.arcSet k := by
  have hI1 : (recip R).φs (Fin.castSucc (idx R (Fin.rev k))) = 2 * Real.pi - R.φs k.succ := by
    show 2 * Real.pi - R.φs (Fin.rev (Fin.castSucc (Fin.rev k))) = _
    rw [Fin.rev_castSucc, Fin.rev_rev]
  have hI2 : (recip R).φs (Fin.succ (idx R (Fin.rev k))) = 2 * Real.pi - R.φs k.castSucc := by
    show 2 * Real.pi - R.φs (Fin.rev (Fin.succ (Fin.rev k))) = _
    rw [Fin.rev_succ, Fin.rev_rev]
  simp only [RadialRegion.arcSet, RadialRegion.arcIcc, hI1, hI2, Set.image_image, loop_recip R hq]
  ext w
  constructor
  ·
    rintro ⟨φ, hφ, rfl⟩
    obtain ⟨hφ1, hφ2⟩ := hφ
    refine ⟨2 * Real.pi - φ, ⟨by linarith, by linarith⟩, ?_⟩
    show R.loop (2 * Real.pi - φ) = R.loop (-φ)
    exact loop_two_pi_sub R φ
  ·
    rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨hψ1, hψ2⟩ := hψ
    refine ⟨2 * Real.pi - ψ, ⟨by linarith, by linarith⟩, ?_⟩
    show R.loop (-(2 * Real.pi - ψ)) = R.loop ψ
    have h := (loop_two_pi_sub R (2 * Real.pi - ψ)).symm
    convert h
    ring

private lemma arcIcc_recip_idx_rev
  (R : RadialRegion)
  (k : Fin R.N) :
  (recip R).arcIcc (idx R (Fin.rev k)) = (fun t : ℝ => 2 * Real.pi - t) '' R.arcIcc k := by
  have hI1 : (recip R).φs (Fin.castSucc (idx R (Fin.rev k))) = 2 * Real.pi - R.φs k.succ := by
    show 2 * Real.pi - R.φs (Fin.rev (Fin.castSucc (Fin.rev k))) = _
    rw [Fin.rev_castSucc, Fin.rev_rev]
  have hI2 : (recip R).φs (Fin.succ (idx R (Fin.rev k))) = 2 * Real.pi - R.φs k.castSucc := by
    show 2 * Real.pi - R.φs (Fin.rev (Fin.succ (Fin.rev k))) = _
    rw [Fin.rev_succ, Fin.rev_rev]
  simp only [RadialRegion.arcIcc, hI1, hI2]
  ext t
  constructor
  ·
    intro ht
    obtain ⟨ht1, ht2⟩ := ht
    refine ⟨2 * Real.pi - t, ⟨by linarith, by linarith⟩, ?_⟩
    show 2 * Real.pi - (2 * Real.pi - t) = t
    ring
  ·
    rintro ⟨x, hx, rfl⟩
    obtain ⟨hx1, hx2⟩ := hx
    show 2 * Real.pi - x ∈ Set.Icc (2 * Real.pi - R.φs k.succ) (2 * Real.pi - R.φs k.castSucc)
    exact ⟨by linarith, by linarith⟩

private lemma arcEquiv_apply
  (R : RadialRegion)
  (k : Fin R.N) : arcEquiv R k = idx R (Fin.rev k) := rfl

private lemma arcIcc_recip_arcEquiv
  (R : RadialRegion)
  (k : Fin R.N) :
  (recip R).arcIcc (arcEquiv R k) = (fun t : ℝ => 2 * Real.pi - t) '' R.arcIcc k := by
  rw [arcEquiv_apply R k]
  exact arcIcc_recip_idx_rev R k

private lemma image_inv_arcSet_arcEquiv
  (R : RadialRegion)
  (hq : R.q = 0) (k : Fin R.N) :
  (fun w : ℂ => w⁻¹) '' (recip R).arcSet (arcEquiv R k) = R.arcSet k := by
  rw [arcEquiv_apply R k]
  exact image_inv_arcSet R hq k

private lemma exists_recip
  (R : RadialRegion)
-- given
  (hq : R.q = 0) :
-- imply
  ∃ R' : RadialRegion,
      R'.q = 0 ∧ R'.N = R.N ∧ (0 : ℂ) ∈ R'.Kint ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ R'.K ↔ w⁻¹ ∉ R.Kint)) ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ R'.Kint ↔ w⁻¹ ∉ R.K)) ∧
      (∀ θ : ℝ, R'.loop θ = (R.loop (2 * π - θ))⁻¹) ∧
      ∃ σ : Fin R.N ≃ Fin R'.N,
        (∀ k : Fin R.N, R'.arcIcc (σ k) = (fun t : ℝ => 2 * π - t) '' R.arcIcc k) ∧
        (∀ k : Fin R.N, (fun w : ℂ => w⁻¹) '' R'.arcSet (σ k) = R.arcSet k) :=
-- proof
  ⟨recip R, recip_q R, recip_N R, zero_mem_Kint R, fun _ hw => mem_K_iff R hq hw,
    fun _ hw => mem_Kint_iff R hq hw, loop_recip_eq R hq, arcEquiv R, arcIcc_recip_arcEquiv R,
    image_inv_arcSet_arcEquiv R hq⟩

@[path]
private lemma main
  {R : RadialRegion}
-- given
  (hq : R.q = 0) :
-- imply
  ∃ R' : RadialRegion,
      R'.q = 0 ∧ R'.N = R.N ∧ (0 : ℂ) ∈ R'.Kint ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ R'.K ↔ w⁻¹ ∉ R.Kint)) ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ R'.Kint ↔ w⁻¹ ∉ R.K)) ∧
      (∀ θ : ℝ, R'.loop θ = (R.loop (2 * π - θ))⁻¹) ∧
      ∃ σ : Fin R.N ≃ Fin R'.N,
        (∀ k : Fin R.N, R'.arcIcc (σ k) = (fun t : ℝ => 2 * π - t) '' R.arcIcc k) ∧
        (∀ k : Fin R.N, (fun w : ℂ => w⁻¹) '' R'.arcSet (σ k) = R.arcSet k) :=
-- proof
  exists_recip (R := R) (hq := hq)


-- created on 2026-10-24
