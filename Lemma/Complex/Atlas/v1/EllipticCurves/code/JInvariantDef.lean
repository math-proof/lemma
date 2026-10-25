import Mathlib
import sympy.Basic
import Def.v1.Atlas.EllipticCurves.code.JInvariantDef
open JInvariant


namespace JInvariant

variable [Field k]
/--
[shortWeierstrassCurve_c₄](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/JInvariantDef.lean)
-/
@[path]
lemma shortWeierstrassCurve_c₄ (A B : k) :
  (shortWeierstrassCurve A B).c₄ = -48 * A := by
  simp only [shortWeierstrassCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]
  ring

end JInvariant

namespace JInvariant

variable [Field k]
/--
[shortWeierstrassCurve_Δ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/JInvariantDef.lean)
-/
@[path]
$-16(4A^3 + 27B^2)$. -/
@[simp]
lemma shortWeierstrassCurve_Δ (A B : k) :
  (shortWeierstrassCurve A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  simp only [shortWeierstrassCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

end JInvariant

namespace JInvariant

/--
[sixteen_ne_zero_of_two_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/JInvariantDef.lean)
-/
@[path]
lemma sixteen_ne_zero_of_two_ne_zero
  [Field k]
-- given
  (h2 : (2 : k) ≠ 0) :
-- imply
  (16 : k) ≠ 0 := by
-- proof
  have : (16 : k) = 2 ^ 4 := by norm_num
  rw [this]; exact pow_ne_zero 4 h2

end JInvariant

namespace JInvariant

/--
[shortWeierstrassCurve_isElliptic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/JInvariantDef.lean)
-/
@[path]
lemma shortWeierstrassCurve_isElliptic
  [Field k]
  {A B : k}
-- given
  (h2 : (2 : k) ≠ 0)
  (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
-- imply
  (shortWeierstrassCurve A B).IsElliptic := by
-- proof
  constructor
  rw [isUnit_iff_ne_zero, shortWeierstrassCurve_Δ]
  exact mul_ne_zero (neg_ne_zero.mpr (sixteen_ne_zero_of_two_ne_zero h2)) hΔ

end JInvariant

namespace JInvariant

/--
[j_eq_jInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/JInvariantDef.lean)
-/
@[path]
lemma j_eq_jInvariant
  [Field k]
  {A B : k}
-- given
  (h2 : (2 : k) ≠ 0)
  (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
-- imply
  haveI :=
-- proof
  shortWeierstrassCurve_isElliptic A B h2 hΔ
    (shortWeierstrassCurve A B).j = jInvariant A B := by
    haveI := shortWeierstrassCurve_isElliptic A B h2 hΔ
    simp only [WeierstrassCurve.j, jInvariant]
    have hΔ_val : ((shortWeierstrassCurve A B).Δ' : k) = (shortWeierstrassCurve A B).Δ :=
      WeierstrassCurve.coe_Δ' _
    simp only [Units.val_inv_eq_inv_val, hΔ_val, shortWeierstrassCurve_Δ,
      shortWeierstrassCurve_c₄]
    have h16 : (16 : k) ≠ 0 := sixteen_ne_zero_of_two_ne_zero h2
    field_simp
    ring

end JInvariant

namespace JInvariant

/--
[jInvariant_of_A_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/JInvariantDef.lean)
-/
@[path]
lemma jInvariant_of_A_eq_zero
  [Field k]
  {B : k} :
-- imply
  jInvariant (0 : k) B = 0 := by
-- proof
  simp [jInvariant]

end JInvariant

namespace JInvariant

/--
[jInvariant_of_B_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/JInvariantDef.lean)
-/
@[path]
lemma jInvariant_of_B_eq_zero
  [Field k]
  {A : k}
-- given
  (hA : A ≠ 0)
  (h2 : (2 : k) ≠ 0) :
-- imply
  jInvariant A (0 : k) = 1728 := by
-- proof
  simp only [jInvariant, mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    add_zero]
  rw [mul_div_cancel_right₀]
  have h4 : (4 : k) ≠ 0 := by
    have : (4 : k) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero 2 h2
  exact mul_ne_zero h4 (pow_ne_zero 3 hA)

end JInvariant

/--
[shortWeierstrassCurve_c](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/JInvariantDef.lean)
-/
@[path]
private lemma shortWeierstrassCurve_c_eq
  [Field k]
  {A B : k} :
-- imply
  (shortWeierstrassCurve A B).c₄ = -48 * A := by
-- proof
  apply JInvariant.shortWeierstrassCurve_c A B

/--
[shortWeierstrassCurve_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/JInvariantDef.lean)
-/
@[path]
private lemma shortWeierstrassCurve__eq
  [Field k]
  {A B : k} :
-- imply
  (shortWeierstrassCurve A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
-- proof
  apply JInvariant.shortWeierstrassCurve_ A B


-- created on 2026-10-23
