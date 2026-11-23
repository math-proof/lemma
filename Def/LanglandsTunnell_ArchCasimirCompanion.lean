import Def.AutomorphicForm_ArchDerivCasimir

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.Converse.ArchCasimir

def matrixFlowDeriv (d : AutomorphicForm.ArchDir) (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) :
    Matrix (Fin 2) (Fin 2) ℝ → ℂ :=
  fun x => deriv (fun t : ℝ => W (x * (AutomorphicForm.archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))) 0

def matrixCasimir (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) : Matrix (Fin 2) (Fin 2) ℝ → ℂ :=
  -((1 / 4 : ℂ) • matrixFlowDeriv .H (matrixFlowDeriv .H W) - (1 / 2 : ℂ) • matrixFlowDeriv .H W +
    matrixFlowDeriv .E (matrixFlowDeriv .Fm W))

structure CasimirDatum (P : RealArchParam) where
  W : Matrix (Fin 2) (Fin 2) ℝ → ℂ

def IsCasimirEigen {P : RealArchParam} (d : CasimirDatum P) : Prop :=
  ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → matrixCasimir d.W x = P.laplaceEigenvalue * d.W x


def zeroDatum (P : RealArchParam) : CasimirDatum P := ⟨fun _ => 0⟩

end LanglandsTunnell.Converse.ArchCasimir

end
