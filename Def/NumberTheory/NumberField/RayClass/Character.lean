/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean -/

import Def.NumberTheory.NumberField.RayClass.Group
import Lemma.Nat.NumberField.RayClass.Group
import Mathlib.Analysis.Complex.Circle
import Abbrev.NumberTheory.NumberField.RayClass.Character
@[expose] noncomputable section

open scoped nonZeroDivisors

/-!
# Ray class characters (N427 Definition 22.10)

A ray class character of a modulus `m` is a homomorphism from the
ray class group to the unit circle. We provide the trivial character,
the pullback to coprime fractional ideals, complex-valued evaluation,
and the extension by zero to all fractional ideals.
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

variable {m : Modulus K}

/-- The trivial ray class character. -/
def trivialCharacter (m : Modulus K) : RayClassCharacter m := 1

/-- Pullback of a ray class character to coprime fractional ideals. -/
def pullback (chi : RayClassCharacter m) :
    coprimeFractionalIdeals m →* Circle :=
  chi.comp (rayClassMap m)

/-- Complex-valued evaluation of a ray class character. -/
def evalComplex (chi : RayClassCharacter m) (x : RayClassGroup m) : ℂ :=
  Circle.coeHom (chi x)

open Classical in
/-- Extension by zero to all (unit) fractional ideals. -/
noncomputable def extendByZero (chi : RayClassCharacter m)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ :=
  if h : I ∈ coprimeFractionalIdeals m then
    Circle.coeHom (chi (rayClassMap m ⟨I, h⟩))
  else
    0

end Modulus
end NumberField
