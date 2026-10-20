import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.Marden
open MetaMathlibExt


/--
[marden](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Marden.lean)
-/
@[path]
private lemma marden_eq
  :
-- imply
  ∀ (a b c : ℂ),
    ((b - a) / (c - a)).im ≠ 0 →
    ∃ (f1 f2 : ℂ) (L : ℝ),
    Polynomial.roots (Polynomial.derivative
    ((Polynomial.X - Polynomial.C a) *
    (Polynomial.X - Polynomial.C b) *
    (Polynomial.X - Polynomial.C c))) = {f1, f2} ∧
    ‖(a + b) / 2 - f1‖ + ‖(a + b) / 2 - f2‖ = L ∧
    ‖(b + c) / 2 - f1‖ + ‖(b + c) / 2 - f2‖ = L ∧
    ‖(c + a) / 2 - f1‖ + ‖(c + a) / 2 - f2‖ = L ∧
    (∀ t : ℝ, t ≠ 0 →
    L < ‖(a + b) / 2 + (t : ℂ) * (b - a) - f1‖ +
    ‖(a + b) / 2 + (t : ℂ) * (b - a) - f2‖) ∧
    (∀ t : ℝ, t ≠ 0 →
    L < ‖(b + c) / 2 + (t : ℂ) * (c - b) - f1‖ +
    ‖(b + c) / 2 + (t : ℂ) * (c - b) - f2‖) ∧
    (∀ t : ℝ, t ≠ 0 →
    L < ‖(c + a) / 2 + (t : ℂ) * (a - c) - f1‖ +
    ‖(c + a) / 2 + (t : ℂ) * (a - c) - f2‖) := by
-- proof
  apply MetaMathlibExt.marden


-- created on 2026-10-20
