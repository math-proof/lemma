module

public import Def.AutomorphicForm_GodementSection
public import Def.AutomorphicForm_WeylIntertwining
public import Abbrev.AutomorphicForm_UnipotentQuotient
public import Def.AutomorphicForm_WindowedSiegelSet
public import Def.LanglandsTunnell_TateLocalZeta

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel

@[expose] public noncomputable section

namespace LanglandsTunnell.RankinSelberg

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section Global

variable (F : Type) [Field F] [NumberField F]

end Global

section Local

abbrev unipotentSubgroup (K : Type*) [CommRing K] : Subgroup (GL (Fin 2) K) :=
  (unipotentGL2Hom (R := K)).range

end Local

end LanglandsTunnell.RankinSelberg

end
