import Def.LanglandsTunnell_JLConverse
import Lemma.AutomorphicForm.ArchDerivCasimir
import Def.LanglandsTunnell_ArchCasimirCompanion

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.Converse.ArchCasimir


theorem matrixFlowDeriv_const (d : AutomorphicForm.ArchDir) (c : ℂ) :
    matrixFlowDeriv d (fun _ => c) = fun _ => 0 := by
  funext x
  simp [matrixFlowDeriv]

theorem matrixCasimir_const (c : ℂ) : matrixCasimir (fun _ => c) = fun _ => 0 := by
  funext x
  simp [matrixCasimir, matrixFlowDeriv_const]


theorem isCasimirEigen_zero (P : RealArchParam) : IsCasimirEigen (zeroDatum P) := by
  intro x _
  show matrixCasimir (fun _ => (0 : ℂ)) x = P.laplaceEigenvalue * 0
  rw [matrixCasimir_const]
  simp

end LanglandsTunnell.Converse.ArchCasimir

end
