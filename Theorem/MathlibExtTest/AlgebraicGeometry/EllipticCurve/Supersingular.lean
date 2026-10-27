/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/Supersingular.lean -/


import Theorem.AlgebraicGeometry.EllipticCurve.Supersingular
attribute [local instance] Classical.decEq


namespace WeierstrassCurve.Affine

example {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve.Affine (AlgebraicClosure (ZMod p))) [W.IsElliptic]
    (h : W.IsSupersingular) {r : ℕ} (hr : 0 < r) {P : W.Point}
    (hP : (p ^ r) • P = 0) : P = 0 :=
  h.pow_torsion W hr hP

example {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve.Affine (AlgebraicClosure (ZMod p))) [W.IsElliptic]
    (h : ∀ r : ℕ, 0 < r → ∀ P : W.Point, (p ^ r) • P = 0 → P = 0) :
    W.IsSupersingular :=
  IsSupersingular.of_pow_torsion W h

example {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve.Affine (AlgebraicClosure (ZMod p))) [W.IsElliptic]
    (h : W.IsSupersingular) (P : W.Point) (hP : p • P = 0) : P = 0 :=
  h P hP

end WeierstrassCurve.Affine
