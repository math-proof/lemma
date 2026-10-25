import Lemma.LanglandsTunnell.CubicInduction_ArchSmoothSpace3

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LanglandsTunnell.CubicInduction.WhittakerBlock

abbrev envelopingAlgebra3 : Type := UniversalEnvelopingAlgebra ℂ (Matrix (Fin 3) (Fin 3) ℂ)

end LanglandsTunnell.CubicInduction.WhittakerBlock
