import Mathlib
import Lemma.Definitions.Def_WeierstrassCurve_VeluOrderTwo

set_option autoImplicit false

namespace WeierstrassCurve

section KernelData

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsShortNF]

lemma veluGx_of_isShortNF (x y : R) : W.veluGx x y = 3 * x ^ 2 + W.a₄ := by
  simp only [veluGx, a₁_of_isShortNF, a₂_of_isShortNF]
  ring

lemma veluGy_zero_of_isShortNF (x : R) : W.veluGy x 0 = 0 := by
  simp only [veluGy, a₁_of_isShortNF, a₃_of_isShortNF]
  ring

lemma velu2QuadDisc_of_isShortNF (x : R) :
    W.velu2QuadDisc x = -16 * (3 * x ^ 2 + 4 * W.a₄) := by
  simp only [velu2QuadDisc, b₂_of_isShortNF, b₄_of_isShortNF]
  ring

lemma equation_zero_iff_of_isShortNF (e : R) :
    W.toAffine.Equation e 0 ↔ e ^ 3 + W.a₄ * e + W.a₆ = 0 := by
  rw [Affine.equation_iff]
  constructor <;> intro h <;>
    linear_combination -h - e ^ 2 * a₂_of_isShortNF W

instance instIsShortNFMk (a b : R) : (WeierstrassCurve.mk 0 0 0 a b).IsShortNF :=
  ⟨rfl, rfl, rfl⟩

end KernelData

section ShortQuotient

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsShortNF]

instance veluQuotient2_isShortNF (x₀ y₀ : R) : (W.veluQuotient2 x₀ y₀).IsShortNF where
  a₁ := a₁_of_isShortNF W
  a₂ := a₂_of_isShortNF W
  a₃ := a₃_of_isShortNF W

lemma veluQuotient2_a₄_of_isShortNF (e : R) :
    (W.veluQuotient2 e 0).a₄ = -(15 * e ^ 2 + 4 * W.a₄) := by
  rw [veluQuotient2_a₄, veluGx_of_isShortNF]
  ring

lemma veluQuotient2_a₆_of_isShortNF (e : R) :
    (W.veluQuotient2 e 0).a₆ = W.a₆ - 21 * e ^ 3 - 7 * W.a₄ * e := by
  rw [veluQuotient2_a₆, veluGx_of_isShortNF, b₂_of_isShortNF]
  ring

theorem veluQuotient2_eq_of_isShortNF (e : R) :
    W.veluQuotient2 e 0
      = ⟨0, 0, 0, -(15 * e ^ 2 + 4 * W.a₄), W.a₆ - 21 * e ^ 3 - 7 * W.a₄ * e⟩ := by
  ext
  · exact a₁_of_isShortNF W
  · exact a₂_of_isShortNF W
  · exact a₃_of_isShortNF W
  · exact veluQuotient2_a₄_of_isShortNF W e
  · exact veluQuotient2_a₆_of_isShortNF W e

end ShortQuotient

end WeierstrassCurve
