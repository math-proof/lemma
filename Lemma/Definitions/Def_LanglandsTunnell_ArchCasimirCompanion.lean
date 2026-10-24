import Lemma.Definitions.Def_LanglandsTunnell_JLConverse
import Lemma.Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.Converse.ArchCasimir

def matrixFlowDeriv (d : AutomorphicForm.ArchDir) (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) :
    Matrix (Fin 2) (Fin 2) ℝ → ℂ :=
  fun x => deriv (fun t : ℝ => W (x * (AutomorphicForm.archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))) 0

def matrixCasimir (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) : Matrix (Fin 2) (Fin 2) ℝ → ℂ :=
  -((1 / 4 : ℂ) • matrixFlowDeriv .H (matrixFlowDeriv .H W) - (1 / 2 : ℂ) • matrixFlowDeriv .H W +
    matrixFlowDeriv .E (matrixFlowDeriv .Fm W))

def IsCasimirEigen {P : RealArchParam} (d : ArchDatumR P) : Prop :=
  ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → matrixCasimir d.W x = P.laplaceEigenvalue * d.W x

theorem matrixFlowDeriv_const (d : AutomorphicForm.ArchDir) (c : ℂ) :
    matrixFlowDeriv d (fun _ => c) = fun _ => 0 := by
  funext x
  simp [matrixFlowDeriv]

theorem matrixCasimir_const (c : ℂ) : matrixCasimir (fun _ => c) = fun _ => 0 := by
  funext x
  simp [matrixCasimir, matrixFlowDeriv_const]

def zeroDatum (P : RealArchParam) : ArchDatumR P where
  W := fun _ => 0
  smooth := show ContDiffOn ℝ (⊤ : ℕ∞) (fun _ => (0 : ℂ)) ArchR.glSet from contDiffOn_const
  unip_law := fun _ _ => (mul_zero _).symm
  central_law := fun _ _ _ => (mul_zero _).symm
  zetaEntire := fun _ _ _ _ => 0
  zetaEntire_differentiable := fun _ _ _ => differentiable_const 0
  zeta_abscissa := 0
  zeta_integrable := fun g u a s _ _ => by
    have h : ArchR.zetaIntegrand (fun _ => (0 : ℂ)) g u a s = fun _ => 0 := funext fun y => by
      simp [ArchR.zetaIntegrand]
    rw [h]
    exact MeasureTheory.integrable_zero _ _ _
  zeta_eq := fun _ _ _ _ _ _ => by simp [ArchR.zetaIntegrand]
  functional_equation := fun _ _ _ _ _ => (mul_zero _).symm
  zetaEntire_finiteOrder := fun _ _ _ _ _ => ⟨0, 0, fun _ _ _ => by simp⟩
  decay_top := fun _ _ => ⟨0, fun _ _ _ _ => by
    rw [show ArchR.asPi (fun _ => (0 : ℂ)) = fun _ => 0 from rfl, iteratedFDerivWithin_fun_zero]
    simp⟩
  decay_zero := fun _ => ⟨0, 0, fun _ _ _ _ _ => by
    rw [show ArchR.asPi (fun _ => (0 : ℂ)) = fun _ => 0 from rfl, iteratedFDerivWithin_fun_zero]
    simp⟩

theorem isCasimirEigen_zero (P : RealArchParam) : IsCasimirEigen (zeroDatum P) := by
  intro x _
  show matrixCasimir (fun _ => (0 : ℂ)) x = P.laplaceEigenvalue * 0
  rw [matrixCasimir_const]
  simp

end LanglandsTunnell.Converse.ArchCasimir

end
