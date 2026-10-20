/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.Group
import Mathlib.Analysis.Complex.Circle

/-!
# Ray class characters (N427 Definition 22.10)

A ray class character of a modulus `m` is a homomorphism from the
ray class group to the unit circle. We provide the trivial character,
the pullback to coprime fractional ideals, complex-valued evaluation,
and the extension by zero to all fractional ideals.
-/

@[expose] noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

variable {m : Modulus K}

/-- A ray class character: homomorphism from the ray class group to `Circle`. -/
abbrev RayClassCharacter (m : Modulus K) := RayClassGroup m →* Circle

/-- The trivial ray class character. -/
def trivialCharacter (m : Modulus K) : RayClassCharacter m := 1

@[simp]
theorem trivialCharacter_apply (m : Modulus K) (x : RayClassGroup m) :
    trivialCharacter m x = 1 :=
  rfl

@[simp]
theorem RayClassCharacter_apply_one (chi : RayClassCharacter m) :
    chi 1 = 1 :=
  map_one chi

@[simp]
theorem RayClassCharacter_apply_mul (chi : RayClassCharacter m)
    (a b : RayClassGroup m) :
    chi (a * b) = chi a * chi b :=
  map_mul chi a b

/-- Pullback of a ray class character to coprime fractional ideals. -/
def pullback (chi : RayClassCharacter m) :
    coprimeFractionalIdeals m →* Circle :=
  chi.comp (rayClassMap m)

@[simp]
theorem pullback_apply (chi : RayClassCharacter m)
    (x : coprimeFractionalIdeals m) :
    pullback chi x = chi (rayClassMap m x) :=
  rfl

@[simp]
theorem pullback_one (chi : RayClassCharacter m) :
    pullback chi 1 = 1 :=
  map_one _

@[simp]
theorem pullback_mul (chi : RayClassCharacter m)
    (a b : coprimeFractionalIdeals m) :
    pullback chi (a * b) = pullback chi a * pullback chi b :=
  map_mul _ _ _

/-- A coprime ideal lying in the ray group evaluates to `1`. -/
theorem pullback_eq_one_of_mem_rayGroup (chi : RayClassCharacter m)
    (x : coprimeFractionalIdeals m) (h : x ∈ rayGroup m) :
    pullback chi x = 1 := by
  rw [pullback_apply, (rayClassMap_eq_one_iff m x).mpr h, map_one]

/-- Complex-valued evaluation of a ray class character. -/
def evalComplex (chi : RayClassCharacter m) (x : RayClassGroup m) : ℂ :=
  Circle.coeHom (chi x)

@[simp]
theorem evalComplex_one (chi : RayClassCharacter m) :
    evalComplex chi 1 = 1 := by
  simp only [evalComplex, map_one]

@[simp]
theorem evalComplex_mul (chi : RayClassCharacter m)
    (a b : RayClassGroup m) :
    evalComplex chi (a * b) = evalComplex chi a * evalComplex chi b := by
  simp only [evalComplex, map_mul]

/-- Evaluation is `1` on the image of the ray group. -/
theorem evalComplex_rayGroup (chi : RayClassCharacter m)
    (x : coprimeFractionalIdeals m) (h : x ∈ rayGroup m) :
    evalComplex chi (rayClassMap m x) = 1 := by
  rw [(rayClassMap_eq_one_iff m x).mpr h, evalComplex_one]

open Classical in
/-- Extension by zero to all (unit) fractional ideals. -/
noncomputable def extendByZero (chi : RayClassCharacter m)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ :=
  if h : I ∈ coprimeFractionalIdeals m then
    Circle.coeHom (chi (rayClassMap m ⟨I, h⟩))
  else
    0

open Classical in
@[simp]
theorem extendByZero_of_mem (chi : RayClassCharacter m)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : I ∈ coprimeFractionalIdeals m) :
    extendByZero chi I =
      Circle.coeHom (chi (rayClassMap m ⟨I, h⟩)) := by
  simp [extendByZero, h]

open Classical in
@[simp]
theorem extendByZero_of_not_mem (chi : RayClassCharacter m)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : I ∉ coprimeFractionalIdeals m) :
    extendByZero chi I = 0 := by
  simp [extendByZero, h]

end Modulus
end NumberField
