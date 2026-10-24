import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.MordellWeil
open WeakMordellWeil
open scoped Classical


namespace WeakMordellWeil

/--
[lemma_25_3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/MordellWeil.lean)
-/
@[path]
lemma lemma_25_3
  {a b X Y : ℚ}
-- given
  (hb : b ≠ 0)
  (hdisc : a ^ 2 - 4 * b ≠ 0)
  (hE' : onCurveE' a b X Y) :
-- imply
  inImageOfPhi a b X Y ↔ (mem_QxSq X ∨ (X = 0 ∧ mem_QxSq (a ^ 2 - 4 * b))) := by
-- proof
  constructor
  ·
    rintro ⟨x, y, hE, hx, hXeq, hYeq⟩
    unfold onCurveE at hE
    by_cases hXne : X ≠ 0
    ·
      left
      refine ⟨hXne, y / x, ?_⟩
      rw [hXeq]
      have : (y / x) * (y / x) = y ^ 2 / x ^ 2 := by ring
      rw [this, hE]; field_simp
    ·
      simp only [not_not] at hXne
      right
      refine ⟨hXne, hdisc, a + 2 * x, ?_⟩
      have hX0 : x + a + b / x = 0 := by linarith [hXeq]
      have h_quad : x ^ 2 + a * x + b = 0 := by field_simp at hX0; nlinarith
      nlinarith
  ·
    rintro (⟨hXne, r, hrs⟩ | ⟨hX0, _, d, hds⟩)
    ·
      have hr : r ≠ 0 := by
        intro hr; rw [hr, mul_zero] at hrs; exact hXne hrs
      have hE'_sub : Y ^ 2 = r * r * ((r * r) ^ 2 + (-2 * a) * (r * r) + (a ^ 2 - 4 * b)) := by
        unfold onCurveE' at hE'; rwa [hrs] at hE'
      have hE'r : Y ^ 2 = r ^ 2 * (r ^ 4 - 2 * a * r ^ 2 + a ^ 2 - 4 * b) := by
        nlinarith [hE'_sub]
      set x := (r * r - a + Y / r) / 2 with hx_def
      have key : Y ^ 2 / r ^ 2 = r ^ 4 - 2 * a * r ^ 2 + a ^ 2 - 4 * b := by
        field_simp; linarith [hE'r]
      have h_quad : x ^ 2 + (a - r * r) * x + b = 0 := by
        have step : 4 * (x ^ 2 + (a - r * r) * x + b) =
          Y ^ 2 / r ^ 2 - r ^ 4 + 2 * a * r ^ 2 - a ^ 2 + 4 * b := by
          simp only [hx_def]; field_simp; ring
        linarith [step, key]
      have hxne : x ≠ 0 := by
        intro hx0; simp [hx0] at h_quad; exact hb h_quad
      have h_curve_rw : x ^ 2 + a * x + b = r * r * x := by nlinarith
      refine ⟨x, r * x, ?_, hxne, ?_, ?_⟩
      ·
        unfold onCurveE; rw [h_curve_rw]; ring
      ·
        rw [hrs]; field_simp; nlinarith
      ·
        have hb_eq : b = r * r * x - x ^ 2 - a * x := by nlinarith
        have h1 : r * x * (1 - b / x ^ 2) = r * (x ^ 2 - b) / x := by field_simp
        rw [h1]
        have h2x_eq : 2 * x + a - r * r = Y / r := by
          have : 2 * x * r = (r * r - a) * r + Y := by
            field_simp at hx_def; linarith
          field_simp; linarith
        have h_xsqb : x ^ 2 - b = x * (2 * x + a - r * r) := by nlinarith [hb_eq]
        rw [h_xsqb, h2x_eq]; field_simp
    ·
      have hY0 : Y = 0 := by
        unfold onCurveE' at hE'
        exact sq_eq_zero_iff.mp (by subst hX0; linarith [hE'])
      set x := (-a + d) / 2 with hx_def
      have h_quad : x ^ 2 + a * x + b = 0 := by
        have : 4 * (x ^ 2 + a * x + b) = d * d - (a ^ 2 - 4 * b) := by
          simp only [hx_def]; ring
        linarith [hds]
      have hxne : x ≠ 0 := by
        intro hx0; simp [hx0] at h_quad; exact hb h_quad
      have hXval : x + a + b / x = 0 := by
        field_simp; nlinarith [h_quad]
      refine ⟨x, 0, ?_, hxne, ?_, ?_⟩
      ·
        unfold onCurveE; rw [h_quad]; simp
      ·
        linarith [hXval, hX0]
      ·
        rw [hY0]; ring

end WeakMordellWeil

namespace WeakMordellWeil

/--
[sqfree_divisors_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/MordellWeil.lean)
-/
@[path]
lemma sqfree_divisors_finite
  {B : ℤ}
-- given
  (hB : B ≠ 0) :
-- imply
  Set.Finite {r : ℤ | Squarefree r ∧ r ∣ B} := by
-- proof
  apply Set.Finite.subset
  · show Set.Finite {r : ℤ | r ∣ B}
    letI := UniqueFactorizationMonoid.fintypeSubtypeDvd B hB
    show Finite {x : ℤ // x ∣ B}
    infer_instance
  · intro x ⟨_, hd⟩; exact hd

end WeakMordellWeil

namespace WeakMordellWeil

/--
[corollary_25_6](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/MordellWeil.lean)
-/
@[path]
lemma corollary_25_6
  {a b : ℤ}
-- given
  (hb : b ≠ 0)
  (hdisc : a ^ 2 - 4 * b ≠ 0) :
-- imply
  Set.Finite {r : ℤ | Squarefree r ∧ r ∣ (a ^ 2 - 4 * b)} ∧ Set.Finite {r : ℤ | Squarefree r ∧ r ∣ (16 * b)} :=
-- proof
  ⟨sqfree_divisors_finite _ hdisc, sqfree_divisors_finite _ (by omega)⟩

end WeakMordellWeil


-- created on 2026-10-23
