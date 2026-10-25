import Lemma.AutomorphicForm.ProductionPinsCompact
import Lemma.AutomorphicForm.ArithCuspRealization
import Def.LanglandsTunnell_DeltaLift

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix AutomorphicForm AutomorphicForm.HeckeEigensystem
open scoped ModularForm MatrixGroups

namespace LanglandsTunnell


@[simp] theorem deltaLiftSystem_level : deltaLiftSystem.level = ⊤ := rfl

@[simp] theorem deltaLiftSystem_toRawCentral : deltaLiftSystem.toRawCentral = deltaRawTable :=
  HeckeEigensystem.toRawCentral_ofRawCentral deltaRawTable

end LanglandsTunnell

end
