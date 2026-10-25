import Def.LanglandsTunnell_JLConverse
import Lemma.AutomorphicForm.SmoothingKernel
import Def.LanglandsTunnell_CubicInduction_JacquetVector3

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchR

namespace LanglandsTunnell.CubicInduction


theorem gaussian3_mem_polyGauss3 : gaussian3 ∈ polyGauss3 :=
  ⟨MvPolynomial.C 1, by funext M; simp⟩


theorem jacquetVector3_eq {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    jacquetVector3 D u₃ a₃ a ψ S g =
      quasiChar (u₃ + 1) a₃ (AutomorphicForm.StandardKernel.realMat g).det *
        ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ S g e :=
  rfl

end LanglandsTunnell.CubicInduction

end
