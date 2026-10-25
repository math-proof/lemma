import Abbrev.AutomorphicForm_UnipotentQuotient
import Def.AutomorphicForm_SmoothAutomorphicFnAt
import Def.NumberField_TateGlobalZeta
import Def.AutomorphicForm_WeylIntertwining

open MeasureTheory NumberField AutomorphicForm Matrix

noncomputable section

namespace RSCarrier

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

end Generic

section Arch

abbrev realUnipotent : Subgroup (GL (Fin 2) ℝ) :=
  (unipotentGL2Hom (R := ℝ)).range

end Arch

section Finite

abbrev finUnipotent : Subgroup (finiteAdelicGL2Subgroup ℚ) :=
  (adelicUnipotent ℚ).subgroupOf (finiteAdelicGL2Subgroup ℚ)

end Finite

end RSCarrier

end
