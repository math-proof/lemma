import Abbrev.AutomorphicForm_RationalCentreUnipotentQuotient
import Structure.NumberField_AdelicLevel

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K : Type*) [Field K] [NumberField K]

abbrev rationalDiagOne : Subgroup (AdelicGL2 (𝓞 K) K) :=
  ((globalPoints (𝓞 K) K).comp (diagOne (A := K))).range

abbrev rationalTorus : Subgroup (AdelicGL2 (𝓞 K) K) :=
  rationalCentre K ⊔ rationalDiagOne K

abbrev rationalTorusUnipotent : Subgroup (AdelicGL2 (𝓞 K) K) :=
  rationalTorus K ⊔ adelicUnipotent K

abbrev RationalTorusUnipotentQuotient : Type _ :=
  MulAction.orbitRel.Quotient (rationalTorusUnipotent K) (AdelicGL2 (𝓞 K) K)


end AutomorphicForm

end
