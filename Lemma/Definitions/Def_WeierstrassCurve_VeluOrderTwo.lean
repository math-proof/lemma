import Mathlib
import Lemma.Definitions.Def_WeierstrassCurve_Velu

set_option autoImplicit false

namespace WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def veluQuotient2 (x₀ y₀ : R) : WeierstrassCurve R where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * W.veluGx x₀ y₀
  a₆ := W.a₆ - W.b₂ * W.veluGx x₀ y₀ - 7 * (x₀ * W.veluGx x₀ y₀)

variable (x₀ y₀ : R)

@[simp] lemma veluQuotient2_a₁ : (W.veluQuotient2 x₀ y₀).a₁ = W.a₁ := rfl
@[simp] lemma veluQuotient2_a₂ : (W.veluQuotient2 x₀ y₀).a₂ = W.a₂ := rfl
@[simp] lemma veluQuotient2_a₃ : (W.veluQuotient2 x₀ y₀).a₃ = W.a₃ := rfl
lemma veluQuotient2_a₄ : (W.veluQuotient2 x₀ y₀).a₄ = W.a₄ - 5 * W.veluGx x₀ y₀ := rfl
lemma veluQuotient2_a₆ :
    (W.veluQuotient2 x₀ y₀).a₆ = W.a₆ - W.b₂ * W.veluGx x₀ y₀ - 7 * (x₀ * W.veluGx x₀ y₀) :=
  rfl

lemma veluQuotient2_b₂ : (W.veluQuotient2 x₀ y₀).b₂ = W.b₂ := by
  simp [b₂]

def velu2QuadDisc (x₀ : R) : R :=
  W.b₂ ^ 2 - 8 * W.b₂ * x₀ - 48 * x₀ ^ 2 - 32 * W.b₄

lemma velu2QuadDisc_def (x₀ : R) :
    W.velu2QuadDisc x₀ = W.b₂ ^ 2 - 8 * W.b₂ * x₀ - 48 * x₀ ^ 2 - 32 * W.b₄ := rfl

lemma velu2QuadDisc_eq_disc_cofactor (x₀ : R) :
    W.velu2QuadDisc x₀
      = (W.b₂ + 4 * x₀) ^ 2 - 16 * (4 * x₀ ^ 2 + W.b₂ * x₀ + 2 * W.b₄) := by
  simp only [velu2QuadDisc]; ring

lemma map_velu2QuadDisc {S : Type*} [CommRing S] (f : R →+* S) (x₀ : R) :
    (W.map f).velu2QuadDisc (f x₀) = f (W.velu2QuadDisc x₀) := by
  simp only [velu2QuadDisc, map_b₂, map_b₄, map_sub, map_mul, map_pow, map_ofNat]

end CommRing

end WeierstrassCurve
