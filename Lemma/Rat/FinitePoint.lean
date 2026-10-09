import Mathlib
import sympy.Basic

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

/--
[WeierstrassCurve_Affine_Point_finite_of_finite_field](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_Point_finite_of_finite_field.lean)
-/

private def twfPointToPair {F : Type*} [Field F] (W : Affine F) :
    W.Point → Option (F × F)
  | .zero => none
  | .some x y _ => some (x, y)

private theorem twfPointToPair_injective {F : Type*} [Field F] (W : Affine F) :
    Function.Injective (twfPointToPair W) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · simp [twfPointToPair] at h
  · simp [twfPointToPair] at h
  · simp only [twfPointToPair, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
@[path]
private lemma main
  [Field F] [DecidableEq F] [Finite F]
  {W : Affine F} :
-- imply
  Finite W.Point :=
-- proof
  Finite.of_injective (twfPointToPair W) (twfPointToPair_injective W)


-- created on 2026-10-05
