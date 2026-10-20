/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/FinslerHadwiger.lean -/

import Mathlib.Analysis.InnerProductSpace.PiL2

namespace MetaMathlibExt

private theorem finsler_hadwiger_identity (A B C D E F G O1 O2 P Q : EuclideanSpace ℝ (Fin 2))
    (hD0 : (D - A).ofLp 0 = -((B - A).ofLp 1)) (hD1 : (D - A).ofLp 1 = (B - A).ofLp 0)
    (hC : C = B + D - A)
    (hG0 : (G - A).ofLp 0 = -((E - A).ofLp 1)) (hG1 : (G - A).ofLp 1 = (E - A).ofLp 0)
    (hF : F = E + G - A)
    (hO1 : O1 = (2 : ℝ)⁻¹ • (A + C)) (hO2 : O2 = (2 : ℝ)⁻¹ • (A + F))
    (hP : P = (2 : ℝ)⁻¹ • (B + G)) (hQ : Q = (2 : ℝ)⁻¹ • (D + E)) :
    ‖P - Q‖ = ‖O1 - O2‖ ∧
      ((P - Q).ofLp 0 * (O1 - O2).ofLp 0 +
        (P - Q).ofLp 1 * (O1 - O2).ofLp 1 = 0) ∧
      O1 + O2 = P + Q := by
  subst hC; subst hF; subst hO1; subst hO2; subst hP; subst hQ
  simp only [PiLp.sub_apply] at hD0 hD1 hG0 hG1
  have hD0c : D.ofLp 0 = A.ofLp 0 - (B.ofLp 1 - A.ofLp 1) := by linarith
  have hD1c : D.ofLp 1 = A.ofLp 1 + (B.ofLp 0 - A.ofLp 0) := by linarith
  have hG0c : G.ofLp 0 = A.ofLp 0 - (E.ofLp 1 - A.ofLp 1) := by linarith
  have hG1c : G.ofLp 1 = A.ofLp 1 + (E.ofLp 0 - A.ofLp 0) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have hsq : ‖(2 : ℝ)⁻¹ • (B + G) - (2 : ℝ)⁻¹ • (D + E)‖ ^ 2
        = ‖(2 : ℝ)⁻¹ • (A + (B + D - A)) - (2 : ℝ)⁻¹ • (A + (E + G - A))‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Real.norm_eq_abs, sq_abs]
      rw [hD0c, hD1c, hG0c, hG1c]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  · simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hD0c, hD1c, hG0c, hG1c]
    ring
  · module

/-- Finsler–Hadwiger theorem (shared-vertex squares, centers mid-segment standard
form): two nondegenerate squares `ABCD` and `AEFG` sharing the vertex `A`,
encoded via 90° rotation conditions with `C = B + D - A` and `F = E + G - A`;
with centers `O1 = (A + C) / 2`, `O2 = (A + F) / 2` and cross-segment midpoints
`P = (B + G) / 2`, `Q = (D + E) / 2`, the centers segment `O1O2` and the
mid-segment `PQ` are equal and perpendicular with a common midpoint.
This is the possibly degenerate identity: when the two squares coincide (`B = E`) both
segments are zero. `finsler_hadwiger_of_ne` adds `B ≠ E` and concludes `O1 ≠ O2`, so that
`O1 P O2 Q` is a square as in the source. The hypotheses `B ≠ A` and `E ≠ A` are unused and
keep the source's shape.
Source: https://en.wikipedia.org/wiki/Finsler%E2%80%93Hadwiger_theorem
(statement finsler-hadwiger-s1).
Proves `Wanted` entry `finsler_hadwiger`.
-/
theorem finsler_hadwiger :
    ∀ (A B C D E F G O1 O2 P Q : EuclideanSpace ℝ (Fin 2)),
      B ≠ A →
      E ≠ A →
      (D - A).ofLp 0 = -((B - A).ofLp 1) →
      (D - A).ofLp 1 = (B - A).ofLp 0 →
      C = B + D - A →
      (G - A).ofLp 0 = -((E - A).ofLp 1) →
      (G - A).ofLp 1 = (E - A).ofLp 0 →
      F = E + G - A →
      O1 = (2 : ℝ)⁻¹ • (A + C) →
      O2 = (2 : ℝ)⁻¹ • (A + F) →
      P = (2 : ℝ)⁻¹ • (B + G) →
      Q = (2 : ℝ)⁻¹ • (D + E) →
      ‖P - Q‖ = ‖O1 - O2‖ ∧
        ((P - Q).ofLp 0 * (O1 - O2).ofLp 0 +
          (P - Q).ofLp 1 * (O1 - O2).ofLp 1 = 0) ∧
        O1 + O2 = P + Q := by
  intro A B C D E F G O1 O2 P Q _ _ hD0 hD1 hC hG0 hG1 hF hO1 hO2 hP hQ
  exact finsler_hadwiger_identity A B C D E F G O1 O2 P Q hD0 hD1 hC hG0 hG1 hF hO1 hO2 hP hQ

/-- Finsler–Hadwiger theorem for distinct squares: two squares `ABCD` and `AEFG` sharing the
vertex `A` (encoded as in `finsler_hadwiger`) with `B ≠ E`. The segments `O1O2` and `PQ`
between the centers and between the cross-segment midpoints are equal, perpendicular, share a
midpoint and are nonzero, so `O1 P O2 Q` is a square. This generalizes the source to possibly
degenerate input squares: `B ≠ A` and `E ≠ A` are not assumed, so one of `ABCD` and `AEFG` may
be the single point `A`, in which case `O1 P O2 Q` is a quarter of the other square.
`finsler_hadwiger` is the source-shaped, possibly degenerate form. -/
theorem finsler_hadwiger_of_ne (A B C D E F G O1 O2 P Q : EuclideanSpace ℝ (Fin 2))
    (hBE : B ≠ E)
    (hD0 : (D - A).ofLp 0 = -((B - A).ofLp 1)) (hD1 : (D - A).ofLp 1 = (B - A).ofLp 0)
    (hC : C = B + D - A)
    (hG0 : (G - A).ofLp 0 = -((E - A).ofLp 1)) (hG1 : (G - A).ofLp 1 = (E - A).ofLp 0)
    (hF : F = E + G - A)
    (hO1 : O1 = (2 : ℝ)⁻¹ • (A + C)) (hO2 : O2 = (2 : ℝ)⁻¹ • (A + F))
    (hP : P = (2 : ℝ)⁻¹ • (B + G)) (hQ : Q = (2 : ℝ)⁻¹ • (D + E)) :
    ‖P - Q‖ = ‖O1 - O2‖ ∧
      ((P - Q).ofLp 0 * (O1 - O2).ofLp 0 +
        (P - Q).ofLp 1 * (O1 - O2).ofLp 1 = 0) ∧
      O1 + O2 = P + Q ∧ O1 ≠ O2 := by
  obtain ⟨hnorm, horth, hmid⟩ :=
    finsler_hadwiger_identity A B C D E F G O1 O2 P Q hD0 hD1 hC hG0 hG1 hF hO1 hO2 hP hQ
  refine ⟨hnorm, horth, hmid, fun h => hBE ?_⟩
  subst hC hF hO1 hO2
  simp only [PiLp.sub_apply] at hD0 hD1 hG0 hG1
  have h0 := congrArg (·.ofLp 0) h
  have h1 := congrArg (·.ofLp 1) h
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    linarith
  · simp only [Fin.mk_one, Fin.isValue]
    linarith

end MetaMathlibExt
