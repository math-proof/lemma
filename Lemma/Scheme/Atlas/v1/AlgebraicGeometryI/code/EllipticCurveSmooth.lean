import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.EllipticCurveSmooth
open Polynomial EllipticCurveSmooth
open scoped Polynomial.Bivariate


namespace EllipticCurveSmooth

/--
[weierstrass_irreducible_via_mathlib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticCurveSmooth.lean)
-/
@[path]
lemma weierstrass_irreducible_via_mathlib
  [Field k]
  {a b : k} :
-- imply
  Irreducible (weierstrass a b) := by
-- proof
  rwa [weierstrass_eq_polynomial]

end EllipticCurveSmooth

namespace EllipticCurveSmooth

/--
[shortWeierstrass_disc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticCurveSmooth.lean)
-/
@[path]
lemma shortWeierstrass_disc
  [Field k]
  {a b : k} :
-- imply
  (shortWeierstrass a b).Δ = -16 * (4 * a ^ 3 + 27 * b ^ 2) := by
-- proof
  simp [shortWeierstrass, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

end EllipticCurveSmooth

namespace EllipticCurveSmooth

/--
[shortWeierstrass_disc_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticCurveSmooth.lean)
-/
@[path]
lemma shortWeierstrass_disc_ne_zero
  [Field k]
  {a b : k}
-- given
  (hchar2 : (2 : k) ≠ 0)
  (hdisc : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
-- imply
  (shortWeierstrass a b).Δ ≠ 0 := by
-- proof
  rw [shortWeierstrass_disc]
  have h16 : (16 : k) ≠ 0 := by
    intro h
    apply hchar2
    have : (16 : k) = 2 ^ 4 := by norm_num
    rw [this] at h
    exact pow_eq_zero_iff (by norm_num : 4 ≠ 0) |>.mp h
  exact mul_ne_zero (neg_ne_zero.mpr h16) hdisc

end EllipticCurveSmooth

namespace EllipticCurveSmooth

/--
[shortWeierstrass_equation_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticCurveSmooth.lean)
-/
@[path]
lemma shortWeierstrass_equation_iff
  [Field k]
  {a b x₀ y₀ : k} :
-- imply
  (shortWeierstrass a b).toAffine.Equation x₀ y₀ ↔ y₀ ^ 2 = x₀ ^ 3 + a * x₀ + b := by
-- proof
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [shortWeierstrass]

end EllipticCurveSmooth

namespace EllipticCurveSmooth

/--
[weierstrass_jacobian_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticCurveSmooth.lean)
-/
@[path]
lemma weierstrass_jacobian_smooth
  [Field k]
  {a b : k}
  {x₀ y₀ : k}
-- given
  (hchar2 : (2 : k) ≠ 0)
  (hdisc : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
  (hcurve : y₀ ^ 2 = x₀ ^ 3 + a * x₀ + b) :
-- imply
  ¬(2 * y₀ = 0 ∧ 3 * x₀ ^ 2 + a = 0) := by
-- proof
  intro ⟨hy, hx⟩
  have hy0 : y₀ = 0 := (mul_eq_zero.mp hy).resolve_left hchar2
  rw [hy0, zero_pow (by norm_num : 2 ≠ 0)] at hcurve
  have ha : a = -(3 * x₀ ^ 2) := by linear_combination hx
  have hb : b = 2 * x₀ ^ 3 := by rw [ha] at hcurve; linear_combination -hcurve
  exact hdisc (by rw [ha, hb]; ring)

end EllipticCurveSmooth

namespace EllipticCurveSmooth

/--
[weierstrass_smooth_at_point](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticCurveSmooth.lean)
-/
@[path]
lemma weierstrass_smooth_at_point
  [Field k]
  {a b : k}
  {x₀ y₀ : k}
-- given
  (hchar2 : (2 : k) ≠ 0)
  (hdisc : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
  (hcurve : y₀ ^ 2 = x₀ ^ 3 + a * x₀ + b) :
-- imply
  2 * y₀ ≠ 0 ∨ 3 * x₀ ^ 2 + a ≠ 0 := by
-- proof
  by_contra h
  push Not at h
  exact weierstrass_jacobian_smooth a b hchar2 hdisc x₀ y₀ hcurve ⟨h.1, h.2⟩

end EllipticCurveSmooth

namespace EllipticCurveSmooth

/--
[shortWeierstrass_nonsingular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticCurveSmooth.lean)
-/
@[path]
lemma shortWeierstrass_nonsingular
  [Field k]
  {a b : k}
  {x₀ y₀ : k}
-- given
  (hchar2 : (2 : k) ≠ 0)
  (hdisc : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
  (hcurve : y₀ ^ 2 = x₀ ^ 3 + a * x₀ + b) :
-- imply
  (shortWeierstrass a b).toAffine.Nonsingular x₀ y₀ := by
-- proof
  have heq : (shortWeierstrass a b).toAffine.Equation x₀ y₀ :=
    (shortWeierstrass_equation_iff a b x₀ y₀).mpr hcurve
  exact (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (shortWeierstrass_disc_ne_zero a b hchar2 hdisc)).mp heq

end EllipticCurveSmooth

namespace EllipticCurveSmooth

/--
[shortWeierstrass_nonsingular_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticCurveSmooth.lean)
-/
@[path]
lemma shortWeierstrass_nonsingular_iff
  [Field k]
  {a b x₀ y₀ : k} :
-- imply
  (shortWeierstrass a b).toAffine.Nonsingular x₀ y₀ ↔ (shortWeierstrass a b).toAffine.Equation x₀ y₀ ∧ (-(3 * x₀ ^ 2 + a) ≠ 0 ∨ 2 * y₀ ≠ 0) := by
-- proof
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  simp [shortWeierstrass]

end EllipticCurveSmooth

/--
[weierstrass_eq_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticCurveSmooth.lean)
-/
@[path]
private lemma weierstrass_eq_polynomial_eq
  [Field k]
  {a b : k} :
-- imply
  weierstrass a b = (shortWeierstrass a b).toAffine.polynomial := by
-- proof
  apply EllipticCurveSmooth.weierstrass_eq_polynomial a b

/--
[weierstrass_monic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticCurveSmooth.lean)
-/
@[path]
private lemma weierstrass_monic_eq
  [Field k]
  {a b : k} :
-- imply
  (weierstrass a b).Monic := by
-- proof
  apply EllipticCurveSmooth.weierstrass_monic a b

/--
[weierstrass_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticCurveSmooth.lean)
-/
@[path]
private lemma weierstrass_natDegree_eq
  [Field k]
  {a b : k} :
-- imply
  (weierstrass a b).natDegree = 2 := by
-- proof
  apply EllipticCurveSmooth.weierstrass_natDegree a b

/--
[weierstrass_no_root](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticCurveSmooth.lean)
-/
@[path]
private lemma weierstrass_no_root_eq
  [Field k]
  {a b : k}
  {g : Polynomial k} :
-- imply
  ¬(weierstrass a b).IsRoot g := by
-- proof
  apply EllipticCurveSmooth.weierstrass_no_root a b g

/--
[weierstrass_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticCurveSmooth.lean)
-/
@[path]
private lemma weierstrass_irreducible_eq
  [Field k]
  {a b : k} :
-- imply
  Irreducible (weierstrass a b) := by
-- proof
  apply EllipticCurveSmooth.weierstrass_irreducible a b


-- created on 2026-10-23
