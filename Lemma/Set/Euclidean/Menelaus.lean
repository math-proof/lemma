import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.Menelaus
open MetaMathlibExt


/--
[menelaus_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Menelaus.lean)
-/
@[path]
private lemma menelaus_general_eq
  {A B C D E F : EuclideanSpace ℝ (Fin 2)}
  {AF FB BD DC CE EA : ℝ}
-- given
  (hnc : ¬ ∃ t : ℝ, AffineMap.lineMap A B t = C)
  (hAB : A ≠ B)
  (hFAv : F - A = AF • (B - A))
  (hBFv : B - F = FB • (B - A))
  (hDBv : D - B = BD • (C - B))
  (hCDv : C - D = DC • (C - B))
  (hECv : E - C = CE • (A - C))
  (hAEv : A - E = EA • (A - C))
  (hFB0 : FB ≠ 0)
  (hDC0 : DC ≠ 0)
  (hEA0 : EA ≠ 0) :
-- imply
  (∃ t : ℝ, AffineMap.lineMap D E t = F) ↔ (AF / FB) * (BD / DC) * (CE / EA) = -1 := by
-- proof
  apply MetaMathlibExt.menelaus_general hnc hAB hFAv hBFv hDBv hCDv hECv hAEv hFB0 hDC0 hEA0

/--
[menelaus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Menelaus.lean)
-/
@[path]
private lemma menelaus_eq
  :
-- imply
  ∀ (A B C D E F : EuclideanSpace ℝ (Fin 2)) (AF FB BD DC CE EA : ℝ),
    (¬ ∃ t : ℝ, AffineMap.lineMap A B t = C) →
    A ≠ B → B ≠ C → A ≠ C →
    (∃ tD : ℝ, AffineMap.lineMap B C tD = D) →
    (∃ tE : ℝ, AffineMap.lineMap C A tE = E) →
    (∃ tF : ℝ, AffineMap.lineMap A B tF = F) →
    D ≠ B → D ≠ C → E ≠ C → E ≠ A → F ≠ A → F ≠ B →
    (F - A = AF • (B - A)) →
    (B - F = FB • (B - A)) →
    (D - B = BD • (C - B)) →
    (C - D = DC • (C - B)) →
    (E - C = CE • (A - C)) →
    (A - E = EA • (A - C)) →
    FB ≠ 0 → DC ≠ 0 → EA ≠ 0 →
    ((∃ t : ℝ, AffineMap.lineMap D E t = F) ↔ (AF / FB) * (BD / DC) * (CE / EA) = -1) := by
-- proof
  apply MetaMathlibExt.menelaus


-- created on 2026-10-20
