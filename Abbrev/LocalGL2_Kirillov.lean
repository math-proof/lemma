import Mathlib
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open scoped Classical

noncomputable section

namespace LocalGL2.Kirillov

open AutomorphicForm IsDedekindDomain NumberField

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)
local notation "Fx" => (HeightOneSpectrum.adicCompletion K v)ˣ
local notation "Γ" => (WithZero (Multiplicative ℤ))ˣ

section charGeneric

variable {A : Type*} [AddCommGroup A]

abbrev charAddCommGroup : AddCommGroup (AddChar A ℂ) := inferInstance

abbrev charFintype [Finite A] : Fintype (AddChar A ℂ) := inferInstance

end charGeneric

section fourier

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

end fourier

section kirillovFunction

variable (ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ)
  (S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ))

end kirillovFunction

section uniformiser

variable (ϖ : (HeightOneSpectrum.adicCompletion K v)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion K v) = WithZero.exp (-1 : ℤ))

end uniformiser

end LocalGL2.Kirillov

end
