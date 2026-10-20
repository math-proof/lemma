import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.EulerOI
open scoped InnerProductSpace
open MetaMathlibExt


/--
[euler_oi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/EulerOI.lean)
-/
@[path]
private lemma euler_oi_eq
  :
-- imply
  ∀ (P : Fin 3 → EuclideanSpace ℝ (Fin 2)) (O I F0 F1 F2 : EuclideanSpace ℝ (Fin 2))
    (R r w0 w1 w2 : ℝ),
    AffineIndependent ℝ P →
    (∀ i, dist O (P i) = R) →
    0 ≤ R →
    0 ≤ r →
    F0 ∈ affineSpan ℝ {P 0, P 1} →
    F1 ∈ affineSpan ℝ {P 1, P 2} →
    F2 ∈ affineSpan ℝ {P 2, P 0} →
    dist I F0 = r →
    dist I F1 = r →
    dist I F2 = r →
    ⟪F0 - I, P 1 - P 0⟫_ℝ = 0 →
    ⟪F1 - I, P 2 - P 1⟫_ℝ = 0 →
    ⟪F2 - I, P 0 - P 2⟫_ℝ = 0 →
    0 < w0 → 0 < w1 → 0 < w2 →
    w0 + w1 + w2 = 1 →
    w0 • P 0 + w1 • P 1 + w2 • P 2 = I →
    (dist O I) ^ 2 = R * (R - 2 * r) ∧ R ≥ 2 * r := by
-- proof
  apply MetaMathlibExt.euler_oi


-- created on 2026-10-20
