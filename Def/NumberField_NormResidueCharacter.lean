import Mathlib
import Def.LanglandsTunnell_NormClass
import Lemma.Ideal.RayCharacterData
import Instance.NumberField_NormResidueCharacter
import Abbrev.NumberField_NormResidueCharacter

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace NumberField.NormResidueChar

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply Ideal
open LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K] (m : ℕ) [NeZero m]

def nu : NarrowRayClassGroup K (fm K m) →* (ZMod m)ˣ := normClassChar K m (dvd_refl _)

def chi (ψ : DirichletCharacter ℂ m) : NarrowRayClassGroup K (fm K m) →* ℂ :=
  (Units.coeHom ℂ).comp ((MulChar.toUnitHom ψ).comp (nu K m))

variable {K m}

def paritySet (ψ : DirichletCharacter ℂ m) : Finset {w : InfinitePlace K // w.IsReal} :=
  if ψ (-1) = 1 then ∅ else Finset.univ

section Cyclo

variable {L : Type} [Field L] [NumberField L] [Algebra K L] [IsCyclotomicExtension {m} K L]

variable (K m)

def U0 {ζ : L} (hζ : IsPrimitiveRoot ζ m) : Subgroup (ZMod m)ˣ := (hζ.autToPow K).range

end Cyclo

end NumberField.NormResidueChar

end
