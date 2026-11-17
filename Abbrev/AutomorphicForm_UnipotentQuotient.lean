module

public import Def.AutomorphicForm_ConstantTerm
public import Structure.AutomorphicForm_AdelicLsXi
public import Instance.NumberField_AdelicHaar
public import Def.NumberField_AdelicBox
public import Def.HaarQuotient

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

@[expose] public noncomputable section

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
