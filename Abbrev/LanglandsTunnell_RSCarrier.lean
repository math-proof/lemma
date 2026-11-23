module

public import Abbrev.AutomorphicForm_UnipotentQuotient
public import Def.AutomorphicForm_SmoothAutomorphicFnAt
public import Def.NumberField_TateGlobalZeta
public import Def.AutomorphicForm_WeylIntertwining

open MeasureTheory NumberField AutomorphicForm Matrix

@[expose] public noncomputable section

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
