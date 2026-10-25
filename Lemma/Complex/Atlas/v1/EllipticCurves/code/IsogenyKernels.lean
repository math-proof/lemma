import Mathlib
import sympy.Basic
import Def.v1.Atlas.EllipticCurves.code.IsogenyKernels.Part4
open Polynomial Velu Velu.VeluDeg2Data Velu.VeluOddData


/--
[lemma_5_1_first_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean)
-/
@[path]
lemma lemma_5_1_first_iff
  [Field k]
  {u v : k[X]}
-- given
  (hcop : IsCoprime u v) :
-- imply
  u.wronskian v = 0 ↔ derivative u = 0 ∧ derivative v = 0 :=
-- proof
  hcop.wronskian_eq_zero_iff

/--
[lemma_5_1_second_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean)
-/
@[path]
lemma lemma_5_1_second_iff
  [Field k]
  {u : k[X]} :
-- imply
  derivative u = 0 ↔ ∃ g : k[X], expand k (ringChar k) g = u := by
-- proof
  constructor
  · intro hu
    by_cases hp : ringChar k = 0
    ·
      haveI : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp hp
      rw [hp]
      have hdeg : u.natDegree = 0 := natDegree_eq_zero_of_derivative_eq_zero hu
      rw [eq_C_of_natDegree_eq_zero hdeg]
      exact ⟨C (u.coeff 0), by simp⟩
    ·
      haveI : CharP k (ringChar k) := ringChar.charP k
      exact ⟨contract (ringChar k) u, expand_contract (ringChar k) hu hp⟩
  ·
    intro ⟨g, hg⟩
    rw [← hg, derivative_expand]
    have : (ringChar k : k[X]) = 0 := by rw [← C_eq_natCast]; simp
    rw [this, zero_mul, mul_zero]

/--
[lemma_5_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean)
-/
@[path]
lemma lemma_5_1
  [Field k]
  {u v : k[X]}
-- given
  (hcop : IsCoprime u v) :
-- imply
  u.wronskian v = 0 ↔ (∃ f : k[X], expand k (ringChar k) f = u) ∧ (∃ g : k[X], expand k (ringChar k) g = v) := by
-- proof
  rw [lemma_5_1_first_iff hcop]
  exact ⟨fun ⟨hu, hv⟩ =>
    ⟨(lemma_5_1_second_iff u).mp hu, (lemma_5_1_second_iff v).mp hv⟩,
    fun ⟨hu, hv⟩ =>
      ⟨(lemma_5_1_second_iff u).mpr hu, (lemma_5_1_second_iff v).mpr hv⟩⟩
namespace Velu
variable {k : Type*} [Field k]

namespace Velu.VeluDeg2Data

/--
[kernel_point_on_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean)
-/
@[path]
lemma kernel_point_on_curve
  [Field k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E} :
-- imply
  (0 : k) ^ 2 = d.x₀ ^ 3 + E.A * d.x₀ + E.B := by
-- proof
  linear_combination -d.is_root

end Velu.VeluDeg2Data

namespace Velu

/--
[AffinePoint.wQ_expanded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean)
-/
@[path]
lemma AffinePoint.wQ_expanded
  [Field k]
  {E : ShortWeierstrassCurve k}
  {Q : AffinePoint E} :
-- imply
  Q.wQ = 2 * Q.y ^ 2 + (3 * Q.x ^ 2 + E.A) * Q.x :=
-- proof
  rfl

end Velu

namespace Velu

/--
[AffinePoint.uQ_eq_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean)
-/
@[path]
lemma AffinePoint.uQ_eq_curve
  [Field k]
  {E : ShortWeierstrassCurve k}
  {Q : AffinePoint E} :
-- imply
  Q.uQ = 2 * (Q.x ^ 3 + E.A * Q.x + E.B) := by
-- proof
  simp only [AffinePoint.uQ]
  linear_combination 2 * Q.on_curve

end Velu

namespace Velu

/--
[AffinePoint.wQ_eq_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean)
-/
@[path]
lemma AffinePoint.wQ_eq_curve
  [Field k]
  {E : ShortWeierstrassCurve k}
  {Q : AffinePoint E} :
-- imply
  Q.wQ = 5 * Q.x ^ 3 + 3 * E.A * Q.x + 2 * E.B := by
-- proof
  simp only [AffinePoint.wQ, AffinePoint.uQ, AffinePoint.tQ]
  linear_combination 2 * Q.on_curve

end Velu

/--
[imageCurve_A](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean)
-/
@[path]
private lemma imageCurve_A_eq
  [Field k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E} :
-- imply
  d.imageCurve.A = d.A' := by
-- proof
  apply Velu.VeluDeg2Data.imageCurve_A d

/--
[imageCurve_B](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean)
-/
@[path]
private lemma imageCurve_B_eq
  [Field k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E} :
-- imply
  d.imageCurve.B = d.B' := by
-- proof
  apply Velu.VeluDeg2Data.imageCurve_B d

/--
[AffinePoint.tQ_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean)
-/
@[path]
private lemma tQ_val_eq
  [Field k]
  {E : ShortWeierstrassCurve k}
  {Q : AffinePoint E} :
-- imply
  Q.tQ = 3 * Q.x ^ 2 + E.A := by
-- proof
  apply Velu.AffinePoint.tQ_val Q

/--
[AffinePoint.uQ_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean)
-/
@[path]
private lemma uQ_val_eq
  [Field k]
  {E : ShortWeierstrassCurve k}
  {Q : AffinePoint E} :
-- imply
  Q.uQ = 2 * Q.y ^ 2 := by
-- proof
  apply Velu.AffinePoint.uQ_val Q

/--
[AffinePoint.wQ_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean)
-/
@[path]
private lemma wQ_val_eq
  [Field k]
  {E : ShortWeierstrassCurve k}
  {Q : AffinePoint E} :
-- imply
  Q.wQ = Q.uQ + Q.tQ * Q.x := by
-- proof
  apply Velu.AffinePoint.wQ_val Q

/--
[imageCurve_A](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean)
-/
@[path]
private lemma imageCurve_A_eq_2
  [Field k]
  {E : ShortWeierstrassCurve k}
  {d : VeluOddData E} :
-- imply
  d.imageCurve.A = d.A' := by
-- proof
  apply Velu.VeluOddData.imageCurve_A d

/--
[imageCurve_B](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean)
-/
@[path]
private lemma imageCurve_B_eq_2
  [Field k]
  {E : ShortWeierstrassCurve k}
  {d : VeluOddData E} :
-- imply
  d.imageCurve.B = d.B' := by
-- proof
  apply Velu.VeluOddData.imageCurve_B d


-- created on 2026-10-23
