import Def.AutomorphicForm_ArchDerivCasimirComplex

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

open NumberField NumberField.InfinitePlace.Completion Matrix Complex

variable {F : Type} [Field F] [NumberField F]


def archDirMatrixComplex : ArchDirComplex → Matrix (Fin 2) (Fin 2) ℂ
  | .H => !![1, 0; 0, -1]
  | .E => !![0, 1; 0, 0]
  | .Fm => !![0, 0; 1, 0]
  | .iH => !![I, 0; 0, -I]
  | .iE => !![0, I; 0, 0]
  | .iFm => !![0, 0; I, 0]


def archComplexProjAt {w : InfinitePlace F} (hw : w.IsComplex) : AdelicGL2 (𝓞 F) F →* GL (Fin 2) ℂ :=
  (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw)).toMonoidHom.comp
    ((AdelicLevel.archComponent F w).comp (AdelicLevel.glArch (𝓞 F) F))

end AutomorphicForm

end
