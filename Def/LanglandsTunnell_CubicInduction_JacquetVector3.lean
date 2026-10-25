import Def.LanglandsTunnell_JLConverse
import Lemma.AutomorphicForm.SmoothingKernel

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchR

namespace LanglandsTunnell.CubicInduction

def gaussian3 (M : Matrix (Fin 2) (Fin 3) ℝ) : ℂ :=
  (Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, M i b ^ 2)) : ℂ)

def polyGauss3 : Set (Matrix (Fin 2) (Fin 3) ℝ → ℂ) :=
  {S | ∃ p : MvPolynomial (Fin 2 × Fin 3) ℂ,
    S = fun M => MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p * gaussian3 M}


def godementInner3 (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (h : Matrix (Fin 2) (Fin 2) ℝ) (m : Matrix (Fin 3) (Fin 3) ℝ) : ℂ :=
  ∫ v : Fin 2 → ℝ,
    S (h * Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b]) *
      ψ (AutomorphicForm.StandardKernel.ofReal (-(v 1)))

def jacquetIntegrand3 {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (e : Fin 2 → Fin 2 → ℝ) : ℂ :=
  godementInner3 ψ S (Matrix.of e) (AutomorphicForm.StandardKernel.realMat g) *
    quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
      D.W (diagOne a * (Matrix.of e)⁻¹)

def jacquetVector3 {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : ℂ :=
  quasiChar (u₃ + 1) a₃ (AutomorphicForm.StandardKernel.realMat g).det *
    ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ S g e

end LanglandsTunnell.CubicInduction

end
