module
public import Def.HeckeCharacter_FiniteOrder
public import Theorem.Matrix.AdelicLevel
public import Def.AutomorphicForm_ConstantTerm
public import Theorem.Ideal.GaussTwist
public import Def.Ideal_GaussTwist
set_option autoImplicit false
set_option maxSynthPendingDepth 3


public section

-- Carved from Lemma/Definitions/Def_AutomorphicForm_GaussTwist.lean: instance decls only.

noncomputable section

open NumberField IsDedekindDomain NumberField.AdelicLevel

namespace AutomorphicForm.GaussTwist


section Gauss

variable (F : Type) [Field F] [NumberField F]

open scoped Classical

instance (𝔣 : Ideal (𝓞 F)) : CommGroup (GaussIndex F 𝔣) := Pi.commGroup

instance (𝔣 : Ideal (𝓞 F)) (𝔭 : modulusPrimes F 𝔣) : Finite (LocalGaussFactor F 𝔣 𝔭.1) := by
  have : Finite ((𝔭.1.adicCompletionIntegers F) ⧸
      (IsLocalRing.maximalIdeal (𝔭.1.adicCompletionIntegers F))
        ^ (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣)) :=
    IsLocalRing.isOpen_iff_finite_quotient.mp
      (IsLocalRing.isOpen_maximalIdeal_pow (𝔭.1.adicCompletionIntegers F) _)
  exact instFiniteUnits

instance (𝔣 : Ideal (𝓞 F)) : Fintype (GaussIndex F 𝔣) := by
  have : Finite (GaussIndex F 𝔣) := Pi.finite
  exact Fintype.ofFinite _

end Gauss

end AutomorphicForm.GaussTwist
end
