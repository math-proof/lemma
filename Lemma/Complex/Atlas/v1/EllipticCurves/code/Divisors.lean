import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.EllipticCurves.code.Divisors.Part5
open Finsupp CurveDiv


namespace CurveDiv

/--
[coeff_of_same](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
lemma coeff_of_same
  [DecidableEq P]
  {p : P} :
-- imply
  (of p).coeff p = 1 := by
-- proof
  simp [coeff, of]

end CurveDiv

namespace CurveDiv

/--
[coeff_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
lemma coeff_of_ne
  [DecidableEq P]
  {p q : P}
-- given
  (h : p ≠ q) :
-- imply
  (of p).coeff q = 0 := by
-- proof
  simp [coeff, of, h]

end CurveDiv

namespace CurveDiv

/--
[mem_supp_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
lemma mem_supp_iff
  {D : CurveDiv P}
  {p : P} :
-- imply
  p ∈ D.supp ↔ D.coeff p ≠ 0 := by
-- proof
  simp [supp, coeff, Finsupp.mem_support_iff]

end CurveDiv

namespace CurveDiv

/--
[deg_of](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
lemma deg_of
  [DecidableEq P]
  {p : P} :
-- imply
  deg (of p) = 1 := by
-- proof
  simp [of, deg_single]

end CurveDiv

namespace CurveDiv

/--
[abelJacobiDivAt_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
lemma abelJacobiDivAt_coe
  {Φ : FunctionFieldDiv P}
  {O p : P} :
-- imply
  (abelJacobiDivAt O p : CurveDiv P) = Finsupp.single p 1 - Finsupp.single O 1 :=
-- proof
  rfl

end CurveDiv

namespace CurveDiv

/--
[abelJacobiDivAt_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
lemma abelJacobiDivAt_self
  {Φ : FunctionFieldDiv P}
  {O : P} :
-- imply
  abelJacobiDivAt O O = (0 : DivZero P) := by
-- proof
  apply Subtype.ext; simp [abelJacobiDivAt_coe]

end CurveDiv

namespace CurveDiv

/--
[pointSumHom_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
lemma pointSumHom_apply
  {Φ : FunctionFieldDiv P}
  [AddCommGroup P]
  {D : CurveDiv P} :
-- imply
  pointSumHom P D = D.pointSum :=
-- proof
  rfl

end CurveDiv

namespace CurveDiv

/--
[pointSum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
lemma pointSum_zero
  {Φ : FunctionFieldDiv P}
  [AddCommGroup P] :
-- imply
  pointSum (0 : CurveDiv P) = 0 :=
-- proof
  (pointSumHom P).map_zero

end CurveDiv

namespace CurveDiv

/--
[pointSum_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
lemma pointSum_single
  {Φ : FunctionFieldDiv P}
  [DecidableEq P]
  [AddCommGroup P]
  {p : P}
  {n : ℤ} :
-- imply
  pointSum (Finsupp.single p n : CurveDiv P) = n • p := by
-- proof
  simp [pointSum, Finsupp.sum_single_index, zero_zsmul]

end CurveDiv

namespace CurveDiv

/--
[pointSum_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
lemma pointSum_sub
  {Φ : FunctionFieldDiv P}
  [AddCommGroup P]
  {D₁ D₂ : CurveDiv P} :
-- imply
  (D₁ - D₂).pointSum = D₁.pointSum - D₂.pointSum :=
-- proof
  map_sub (pointSumHom P) D₁ D₂

end CurveDiv

namespace CurveDiv

/--
[pointSum_of](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
lemma pointSum_of
  {Φ : FunctionFieldDiv P}
  [DecidableEq P]
  [AddCommGroup P]
  {p : P} :
-- imply
  (of p).pointSum = p := by
-- proof
  simp [of, pointSum_single]
/-- A principal divisor sums (under the group law of `P`) to `0`. This is one
direction of the Abel-Jacobi isomorphism (Theorem 23.17) for elliptic curves. -/

end CurveDiv

namespace CurveDiv

/--
[abelJacobiDiv_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
lemma abelJacobiDiv_coe
  {Φ : FunctionFieldDiv P}
  [AddCommGroup P]
  {Φ' : FunctionFieldDiv P}
  {p : P} :
-- imply
  (abelJacobiDiv p : CurveDiv P) = Finsupp.single p 1 - Finsupp.single (0 : P) 1 :=
-- proof
  rfl

end CurveDiv

namespace CurveDiv

/--
[abelJacobiDiv_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
lemma abelJacobiDiv_zero
  {Φ : FunctionFieldDiv P}
  [AddCommGroup P]
  {Φ' : FunctionFieldDiv P} :
-- imply
  abelJacobiDiv (0 : P) = (0 : DivZero P) :=
-- proof
  abelJacobiDivAt_self 0

end CurveDiv

/--
[rational_map_is_morphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
lemma rational_map_is_morphism
  {C : SmoothProjectiveCurve}
  {m : ℕ}
  {φ : RationalMap C m}
-- given
  (hm : 0 < m) :
-- imply
  φ.isMorphism := by
-- proof
  intro P
  have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  obtain ⟨i₀, _, hi₀⟩ :=
    Finset.exists_mem_eq_inf' hne (fun i => C.val P (φ.coords i))
  obtain ⟨j, hj⟩ := φ.not_all_zero
  have hmin_ne_top : C.val P (φ.coords i₀) ≠ ⊤ := by
    intro h
    have hle : C.val P (φ.coords i₀) ≤ C.val P (φ.coords j) := by
      rw [← hi₀]; exact Finset.inf'_le _ (Finset.mem_univ j)
    rw [h] at hle
    exact C.val_ne_top P _ hj (WithTop.top_le_iff.mp hle)
  obtain ⟨n_min, hn_min⟩ := WithTop.ne_top_iff_exists.mp hmin_ne_top
  obtain ⟨c, hc_ne, hc_val⟩ := C.val_surj P (-n_min)
  refine ⟨c, hc_ne, fun i => ?_, ⟨i₀, ?_⟩⟩
  ·
    rw [C.val_mul, hc_val]
    have hi_le : C.val P (φ.coords i₀) ≤ C.val P (φ.coords i) := by
      rw [← hi₀]; exact Finset.inf'_le _ (Finset.mem_univ i)
    rw [← hn_min] at hi_le
    cases hv : C.val P (φ.coords i) with
    | top => exact le_top
    | coe k =>
      rw [hv] at hi_le
      simp only [WithTop.coe_le_coe] at hi_le
      rw [← WithTop.coe_add]
      exact WithTop.coe_le_coe.mpr (by omega)
  ·
    rw [C.val_mul, hc_val, ← hn_min, ← WithTop.coe_add]
    simp [neg_add_cancel]

/--
[deg_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
private lemma deg_zero_eq :
-- imply
  deg (0 : CurveDiv P) = 0 := by
-- proof
  apply CurveDiv.deg_zero

/--
[deg_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
private lemma deg_single_eq
  [DecidableEq P]
  {p : P}
  {n : ℤ} :
-- imply
  deg (Finsupp.single p n) = n := by
-- proof
  apply CurveDiv.deg_single p n

/--
[deg_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
private lemma deg_add_eq
  {D₁ D₂ : CurveDiv P} :
-- imply
  (D₁ + D₂).deg = D₁.deg + D₂.deg := by
-- proof
  apply CurveDiv.deg_add D₁ D₂

/--
[mem_divZero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean)
-/
@[path]
private lemma mem_divZero_iff_eq
  {D : CurveDiv P} :
-- imply
  D ∈ DivZero P ↔ D.deg = 0 := by
-- proof
  apply CurveDiv.mem_divZero_iff D


-- created on 2026-10-23
