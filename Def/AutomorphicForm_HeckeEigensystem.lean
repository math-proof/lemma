import Mathlib
import Structure.AutomorphicForm_HeckeEigensystem

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm


namespace HeckeEigensystem

variable {F : Type*} [Field F] [NumberField F] {R : Type*} [CommRing R]

def twist (Φ : HeckeEigensystem F R) (χ : HeightOneSpectrum (𝓞 F) → R) :
    HeckeEigensystem F R where
  level := Φ.level
  level_ne_bot := Φ.level_ne_bot
  a := fun v => χ v * Φ.a v
  b := fun v => χ v ^ 2 * Φ.b v

@[simp] theorem twist_a (Φ : HeckeEigensystem F R) (χ : HeightOneSpectrum (𝓞 F) → R)
    (v : HeightOneSpectrum (𝓞 F)) : (Φ.twist χ).a v = χ v * Φ.a v := rfl

@[simp] theorem twist_b (Φ : HeckeEigensystem F R) (χ : HeightOneSpectrum (𝓞 F) → R)
    (v : HeightOneSpectrum (𝓞 F)) : (Φ.twist χ).b v = χ v ^ 2 * Φ.b v := rfl


end HeckeEigensystem


@[simp] theorem satakePow_zero {R : Type*} [CommRing R] (s e : R) : satakePow 0 s e = 2 := rfl

@[simp] theorem satakePow_one {R : Type*} [CommRing R] (s e : R) : satakePow 1 s e = s := rfl

theorem satakePow_add_two {R : Type*} [CommRing R] (n : ℕ) (s e : R) :
    satakePow (n + 2) s e = s * satakePow (n + 1) s e - e * satakePow n s e := rfl

section Transfer

variable {E L : Type*} [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)]
  {R : Type*} [CommRing R]


def IsDescentOf (Φ : HeckeEigensystem L R) (π : HeckeEigensystem E R) : Prop :=
  IsBaseChangeOf π Φ

end Transfer


end AutomorphicForm

end
