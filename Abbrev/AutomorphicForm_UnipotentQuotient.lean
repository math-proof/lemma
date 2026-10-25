import Def.AutomorphicForm_ConstantTerm
import Structure.AutomorphicForm_AdelicLsXi
import Instance.NumberField_AdelicHaar
import Def.NumberField_AdelicBox
import Def.HaarQuotient

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K : Type*) [Field K] [NumberField K]

abbrev adelicUnipotent : Subgroup (AdelicGL2 (𝓞 K) K) :=
  (unipotentGL2Hom (R := AdeleRing (𝓞 K) K)).range

abbrev UnipotentQuotient : Type _ :=
  MulAction.orbitRel.Quotient (adelicUnipotent K) (AdelicGL2 (𝓞 K) K)

end AutomorphicForm

end
