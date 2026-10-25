import Abbrev.AutomorphicForm_UnipotentQuotient

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K : Type*) [Field K] [NumberField K]

abbrev rationalCentre : Subgroup (AdelicGL2 (𝓞 K) K) :=
  ((globalPoints (𝓞 K) K).comp
    (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom)).range

abbrev rationalCentreUnipotent : Subgroup (AdelicGL2 (𝓞 K) K) :=
  rationalCentre K ⊔ adelicUnipotent K

abbrev RationalCentreUnipotentQuotient : Type _ :=
  MulAction.orbitRel.Quotient (rationalCentreUnipotent K) (AdelicGL2 (𝓞 K) K)


end AutomorphicForm

end
