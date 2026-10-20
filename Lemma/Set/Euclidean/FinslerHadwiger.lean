import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.FinslerHadwiger
open MetaMathlibExt


/--
[finsler_hadwiger](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/FinslerHadwiger.lean)
-/
@[path]
private lemma finsler_hadwiger_eq
  :
-- imply
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
-- proof
  apply MetaMathlibExt.finsler_hadwiger

/--
[finsler_hadwiger_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/FinslerHadwiger.lean)
-/
@[path]
private lemma finsler_hadwiger_of_ne_eq
  {A B C D E F G O1 O2 P Q : EuclideanSpace ℝ (Fin 2)}
-- given
  (hBE : B ≠ E)
  (hD0 : (D - A).ofLp 0 = -((B - A).ofLp 1))
  (hD1 : (D - A).ofLp 1 = (B - A).ofLp 0)
  (hC : C = B + D - A)
  (hG0 : (G - A).ofLp 0 = -((E - A).ofLp 1))
  (hG1 : (G - A).ofLp 1 = (E - A).ofLp 0)
  (hF : F = E + G - A)
  (hO1 : O1 = (2 : ℝ)⁻¹ • (A + C))
  (hO2 : O2 = (2 : ℝ)⁻¹ • (A + F))
  (hP : P = (2 : ℝ)⁻¹ • (B + G))
  (hQ : Q = (2 : ℝ)⁻¹ • (D + E)) :
-- imply
  ‖P - Q‖ = ‖O1 - O2‖ ∧
    ((P - Q).ofLp 0 * (O1 - O2).ofLp 0 +
    (P - Q).ofLp 1 * (O1 - O2).ofLp 1 = 0) ∧
    O1 + O2 = P + Q ∧ O1 ≠ O2 := by
-- proof
  apply MetaMathlibExt.finsler_hadwiger_of_ne A B C D E F G O1 O2 P Q hBE hD0 hD1 hC hG0 hG1 hF hO1 hO2 hP hQ


-- created on 2026-10-20
