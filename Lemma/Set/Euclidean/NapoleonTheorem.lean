import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.NapoleonTheorem
open MetaMathlibExt


/--
[napoleon_theorem_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/NapoleonTheorem.lean)
-/
@[path]
private lemma napoleon_theorem_general_eq
  {A B C A2 B2 C2 G1 G2 G3 : EuclideanSpace ℝ (Fin 2)}
-- given
  (hBA2 : dist B A2 = dist B C)
  (hCA2 : dist C A2 = dist B C)
  (hCB2 : dist C B2 = dist C A)
  (hAB2 : dist A B2 = dist C A)
  (hAC2 : dist A C2 = dist A B)
  (hBC2 : dist B C2 = dist A B)
  (hout1 : ((C.ofLp 0 - B.ofLp 0) * (A.ofLp 1 - B.ofLp 1) - (C.ofLp 1 - B.ofLp 1) * (A.ofLp 0 - B.ofLp 0)) * ((C.ofLp 0 - B.ofLp 0) * (A2.ofLp 1 - B.ofLp 1) - (C.ofLp 1 - B.ofLp 1) * (A2.ofLp 0 - B.ofLp 0)) < 0)
  (hout2 : ((A.ofLp 0 - C.ofLp 0) * (B.ofLp 1 - C.ofLp 1) - (A.ofLp 1 - C.ofLp 1) * (B.ofLp 0 - C.ofLp 0)) * ((A.ofLp 0 - C.ofLp 0) * (B2.ofLp 1 - C.ofLp 1) - (A.ofLp 1 - C.ofLp 1) * (B2.ofLp 0 - C.ofLp 0)) < 0)
  (hout3 : ((B.ofLp 0 - A.ofLp 0) * (C.ofLp 1 - A.ofLp 1) - (B.ofLp 1 - A.ofLp 1) * (C.ofLp 0 - A.ofLp 0)) * ((B.ofLp 0 - A.ofLp 0) * (C2.ofLp 1 - A.ofLp 1) - (B.ofLp 1 - A.ofLp 1) * (C2.ofLp 0 - A.ofLp 0)) < 0)
  (hG1 : G1 = (1 / 3 : ℝ) • (B + C + A2))
  (hG2 : G2 = (1 / 3 : ℝ) • (C + A + B2))
  (hG3 : G3 = (1 / 3 : ℝ) • (A + B + C2)) :
-- imply
  dist G1 G2 = dist G2 G3 ∧ dist G2 G3 = dist G3 G1 ∧ 0 < dist G1 G2 := by
-- proof
  apply MetaMathlibExt.napoleon_theorem_general A B C A2 B2 C2 G1 G2 G3 hBA2 hCA2 hCB2 hAB2 hAC2 hBC2 hout1 hout2 hout3 hG1 hG2 hG3

/--
[napoleon_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/NapoleonTheorem.lean)
-/
@[path]
private lemma napoleon_theorem_eq
  :
-- imply
  ∀ (A B C A2 B2 C2 G1 G2 G3 : EuclideanSpace ℝ (Fin 2)),
    A ≠ B → B ≠ C → C ≠ A →
    ((B.ofLp 0 - A.ofLp 0) * (C.ofLp 1 - A.ofLp 1) -
    (B.ofLp 1 - A.ofLp 1) * (C.ofLp 0 - A.ofLp 0) ≠ 0) →
    dist B A2 = dist B C → dist C A2 = dist B C →
    dist C B2 = dist C A → dist A B2 = dist C A →
    dist A C2 = dist A B → dist B C2 = dist A B →
    (((C.ofLp 0 - B.ofLp 0) * (A.ofLp 1 - B.ofLp 1) -
    (C.ofLp 1 - B.ofLp 1) * (A.ofLp 0 - B.ofLp 0)) *
    ((C.ofLp 0 - B.ofLp 0) * (A2.ofLp 1 - B.ofLp 1) -
    (C.ofLp 1 - B.ofLp 1) * (A2.ofLp 0 - B.ofLp 0)) < 0) →
    (((A.ofLp 0 - C.ofLp 0) * (B.ofLp 1 - C.ofLp 1) -
    (A.ofLp 1 - C.ofLp 1) * (B.ofLp 0 - C.ofLp 0)) *
    ((A.ofLp 0 - C.ofLp 0) * (B2.ofLp 1 - C.ofLp 1) -
    (A.ofLp 1 - C.ofLp 1) * (B2.ofLp 0 - C.ofLp 0)) < 0) →
    (((B.ofLp 0 - A.ofLp 0) * (C.ofLp 1 - A.ofLp 1) -
    (B.ofLp 1 - A.ofLp 1) * (C.ofLp 0 - A.ofLp 0)) *
    ((B.ofLp 0 - A.ofLp 0) * (C2.ofLp 1 - A.ofLp 1) -
    (B.ofLp 1 - A.ofLp 1) * (C2.ofLp 0 - A.ofLp 0)) < 0) →
    G1 = (1 / 3 : ℝ) • (B + C + A2) →
    G2 = (1 / 3 : ℝ) • (C + A + B2) →
    G3 = (1 / 3 : ℝ) • (A + B + C2) →
    dist G1 G2 = dist G2 G3 ∧ dist G2 G3 = dist G3 G1 := by
-- proof
  apply MetaMathlibExt.napoleon_theorem


-- created on 2026-10-20
