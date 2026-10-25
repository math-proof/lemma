import Mathlib
import Instance.ModularCurve_KatzLevelP

set_option autoImplicit false

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP

variable {A B : Type*} [CommRing A] [CommRing B] (W : WeierstrassCurve A)

def smulX (a : ℤ) (x : A) : A :=
  (W.Φ a).eval x * Ring.inverse ((W.ΨSq a).eval x)


variable (p : ℕ)

def veluTLine (x : A) : A :=
  ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), (6 * smulX W a x ^ 2 + W.b₂ * smulX W a x + W.b₄)

def veluWLine (x : A) : A :=
  ∑ a ∈ Finset.Icc 1 ((p - 1) / 2),
    (W.Ψ₂Sq.eval (smulX W a x) + smulX W a x * (6 * smulX W a x ^ 2 + W.b₂ * smulX W a x + W.b₄))

def quotientByLine (x : A) : WeierstrassCurve A where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * veluTLine W p x
  a₆ := W.a₆ - W.b₂ * veluTLine W p x - 7 * veluWLine W p x

end LevelP

namespace LevelPData

variable {A : Type*} [CommRing A] (W : WeierstrassCurve A) (p : ℕ) (D : LevelPData A)

def quotientBySndLine : WeierstrassCurve A := LevelP.quotientByLine W p D.xQ

def quotientByFstLine : WeierstrassCurve A := LevelP.quotientByLine W p D.xP

end LevelPData

end ModularCurve

end
