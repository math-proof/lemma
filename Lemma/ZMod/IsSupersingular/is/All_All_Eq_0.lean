import Mathlib
import sympy.Basic
import sympy.AlgebraicGeometry.EllipticCurve.Supersingular

open WeierstrassCurve.Affine

attribute [local instance] Classical.decEq

/--
[IsSupersingular.iff_pow_torsion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/Supersingular.lean)
-/
@[path]
private lemma iff_pow_torsion_eq
  {p : ℕ} [Fact p.Prime]
-- given
  (W : WeierstrassCurve.Affine (AlgebraicClosure (ZMod p))) [W.IsElliptic] :
-- imply
  W.IsSupersingular ↔
    ∀ r : ℕ, 0 < r → ∀ P : W.Point, (p ^ r) • P = 0 → P = 0 := by
-- proof
  apply IsSupersingular.iff_pow_torsion


/--
[IsSupersingular.of_pow_torsion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/Supersingular.lean)
-/
@[path]
private lemma of_pow_torsion_eq
  {p : ℕ} [Fact p.Prime]
-- given
  (W : WeierstrassCurve.Affine (AlgebraicClosure (ZMod p))) [W.IsElliptic]
  (h : ∀ r : ℕ, 0 < r → ∀ P : W.Point, (p ^ r) • P = 0 → P = 0) :
-- imply
  W.IsSupersingular := by
-- proof
  apply IsSupersingular.of_pow_torsion
  exact h


/--
[IsSupersingular.pow_torsion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/Supersingular.lean)
-/
@[path]
private lemma pow_torsion_eq
  {p : ℕ} [Fact p.Prime]
-- given
  (W : WeierstrassCurve.Affine (AlgebraicClosure (ZMod p))) [W.IsElliptic]
  (h : W.IsSupersingular) {r : ℕ} (hr : 0 < r)
  {P : W.Point} (hP : (p ^ r) • P = 0) :
-- imply
  P = 0 := by
-- proof
  apply IsSupersingular.pow_torsion
  · exact h
  · exact hr
  · exact hP


-- created on 2026-10-09
