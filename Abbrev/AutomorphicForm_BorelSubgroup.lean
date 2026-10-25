import Structure.AutomorphicForm_AdelicLsXi
import Def.AutomorphicForm_ConstantTerm

noncomputable section

namespace AutomorphicForm

section BorelCommRing

variable (A : Type*) [CommRing A]


end BorelCommRing

section AdelicBorel

open NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

abbrev adelicBorel : Subgroup (AdelicGL2 R K) := borelSubgroup (AdeleRing R K)

end AdelicBorel

end AutomorphicForm

end
