import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[betweenness_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/InterceptTheorem.lean)
-/
@[path]
private lemma betweenness_ratio {P Q R : EuclideanSpace ℝ (Fin 2)}
  (h : dist P Q + dist Q R = dist P R)
  (h1 : 0 < dist P Q) (h2 : 0 < dist Q R) :
  ∃ s : ℝ, 0 < s ∧ s < 1 ∧ Q - P = s • (R - P) ∧
    dist P Q = s * dist P R ∧ dist Q R = (1 - s) * dist P R := by
  have hPR : 0 < dist P R := by linarith
  have hPRne : dist P R ≠ 0 := ne_of_gt hPR
  have hQRne : dist Q R ≠ 0 := ne_of_gt h2
  refine ⟨dist P Q / dist P R, div_pos h1 hPR, ?_, ?_, ?_, ?_⟩
  · rw [div_lt_one hPR]
    linarith
  · have huv : (Q - P) + (R - Q) = R - P := by abel
    have hnu : ‖Q - P‖ = dist P Q := by
      rw [dist_eq_norm, norm_sub_rev]
    have hnv : ‖R - Q‖ = dist Q R := by
      rw [dist_eq_norm, norm_sub_rev]
    have hnw : ‖(Q - P) + (R - Q)‖ = dist P R := by
      rw [huv, dist_eq_norm, norm_sub_rev]
    have hnorm : ‖Q - P‖ + ‖R - Q‖ = ‖(Q - P) + (R - Q)‖ := by
      rw [hnu, hnv, hnw]; exact h
    have hexpand := norm_add_sq_real (Q - P) (R - Q)
    have hsq : (‖Q - P‖ + ‖R - Q‖) ^ 2 = ‖(Q - P) + (R - Q)‖ ^ 2 := by rw [hnorm]
    have hpow : (‖Q - P‖ + ‖R - Q‖) ^ 2
      = ‖Q - P‖ ^ 2 + 2 * (‖Q - P‖ * ‖R - Q‖) + ‖R - Q‖ ^ 2 := by ring
    have hinn : inner ℝ (Q - P) (R - Q) = ‖Q - P‖ * ‖R - Q‖ := by
      rw [hsq, hexpand] at hpow
      linarith
    have hcs := inner_eq_norm_mul_iff_real.mp hinn
    have hau : (0:ℝ) < ‖Q - P‖ := by rw [hnu]; exact h1
    have hav : (0:ℝ) < ‖R - Q‖ := by rw [hnv]; exact h2
    have hbne : (‖R - Q‖ : ℝ) ≠ 0 := ne_of_gt hav
    have hu_eq : Q - P = (dist P Q / dist Q R) • (R - Q) := by
      have e1 : Q - P = ((‖R - Q‖⁻¹ * ‖Q - P‖ : ℝ)) • (R - Q) := by
        have e2 : ((‖R - Q‖⁻¹ * ‖R - Q‖ : ℝ)) • (Q - P) = Q - P := by
          rw [inv_mul_cancel₀ hbne, one_smul]
        have e3 : ((‖R - Q‖⁻¹ * ‖R - Q‖ : ℝ)) • (Q - P)
          = ((‖R - Q‖⁻¹ * ‖Q - P‖ : ℝ)) • (R - Q) := by
          rw [mul_smul, mul_smul, hcs]
        rwa [e2] at e3
      have e4 : (dist P Q / dist Q R : ℝ) = (‖R - Q‖⁻¹ * ‖Q - P‖ : ℝ) := by
        rw [← hnu, ← hnv, div_eq_mul_inv, mul_comm]
      rwa [e4]
    have hc1 : (dist P Q / dist Q R + 1 : ℝ) = dist P R / dist Q R := by
      have e : dist P Q / dist Q R + 1 = (dist P Q + dist Q R) / dist Q R := by
        rw [add_div, div_self hQRne]
      rw [e, h]
    have hsc : (dist P Q / dist P R) * (dist P Q / dist Q R + 1)
      = dist P Q / dist Q R := by
      rw [hc1]
      exact div_mul_div_cancel₀ hPRne
    have hR : R - P = ((dist P Q / dist Q R + 1 : ℝ)) • (R - Q) := by
      rw [← huv, hu_eq, add_smul, one_smul]
    have e : (dist P Q / dist P R) • (R - P)
      = (dist P Q / dist Q R) • (R - Q) := by
      rw [hR, ← mul_smul, hsc]
    rwa [e]
  · rw [div_mul_cancel₀ _ hPRne]
  · have hADs : dist P Q = (dist P Q / dist P R) * dist P R := by
    rw [div_mul_cancel₀ _ hPRne]
    have hmid : (1 - dist P Q / dist P R) * dist P R = dist P R - dist P Q := by
      linear_combination hADs
    rw [hmid]
    linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[intercept_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/InterceptTheorem.lean)
-/
@[path]
lemma intercept_theorem
  :
-- imply
  ∀ (A B C D E : EuclideanSpace ℝ (Fin 2)),
    dist A D + dist D B = dist A B →
    0 < dist A D →
    0 < dist D B →
    dist A E + dist E C = dist A C →
    0 < dist A E →
    0 < dist E C →
    (¬ ∃ t : ℝ, C - A = t • (B - A)) →
    (∃ r : ℝ, r ≠ 0 ∧ E - D = r • (C - B)) →
    dist A D / dist D B = dist A E / dist E C := by
-- proof
  intro A B C D E hD hAD hDB hE hAE hEC hnoncoll hpar_ex
  obtain ⟨s, hs0, hs1, hDs, hADs, hDBs⟩ := betweenness_ratio hD hAD hDB
  obtain ⟨t, ht0, ht1, hEt, hAEs, hECs⟩ := betweenness_ratio hE hAE hEC
  obtain ⟨r, hr0, hpar⟩ := hpar_ex
  have hABpos : 0 < dist A B := by linarith
  have hABne : dist A B ≠ 0 := ne_of_gt hABpos
  have hACpos : 0 < dist A C := by linarith
  have hACne : dist A C ≠ 0 := ne_of_gt hACpos
  have hBA : B - A ≠ 0 := by
    intro hcon
    apply hABne
    have h1 : dist A B = ‖A - B‖ := dist_eq_norm _ _
    have h2 : A - B = -(B - A) := by abel
    rw [h1, h2, hcon, neg_zero, norm_zero]
  have hED : E - D = t • (C - A) - s • (B - A) := by
    have e : (E - A) - (D - A) = E - D := by abel
    rw [← e, hEt, hDs]
  have hCB : C - B = (C - A) - (B - A) := by abel
  rw [hED, hCB] at hpar
  -- hpar : t • (C - A) - s • (B - A) = r • ((C - A) - (B - A))
  have key : (t - r) • (C - A) + (r - s) • (B - A) = 0 := by
    have e : (t - r) • (C - A) + (r - s) • (B - A)
      = (t • (C - A) - s • (B - A)) - r • ((C - A) - (B - A)) := by
      module
    rw [e, hpar, sub_self]
  have htr : t = r := by
    by_contra hne
    apply hnoncoll
    have hne' : (t - r : ℝ) ≠ 0 := sub_ne_zero.mpr hne
    have h2 : (t - r) • (C - A) = -((r - s) • (B - A)) :=
      eq_neg_of_add_eq_zero_left key
    refine ⟨-((r - s) / (t - r)), ?_⟩
    have h1 : C - A = (t - r)⁻¹ • ((t - r) • (C - A)) := by
      rw [← mul_smul, inv_mul_cancel₀ hne', one_smul]
    rw [h1, h2, smul_neg, ← mul_smul, div_eq_mul_inv]
    module
  have hrs : r - s = 0 := by
    rw [htr] at key
    simp only [sub_self, zero_smul, zero_add] at key
    obtain h | h := smul_eq_zero.mp key
    · exact h
    · exact absurd h hBA
  have hst : s = t := by linarith
  have h1s : (1 : ℝ) - s ≠ 0 := by
    have : (0 : ℝ) < 1 - s := by linarith
    exact ne_of_gt this
  rw [hADs, hDBs, hAEs, hECs, hst]
  rw [mul_div_mul_right _ _ hABne, mul_div_mul_right _ _ hACne]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
