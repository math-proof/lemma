/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger/MSS.lean -/

import Def.Analysis.CStarAlgebra.KadisonSinger.MSS
import Lemma.Real.CStarAlgebra.KadisonSinger.MSS
import Theorem.MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.MSS
open scoped BigOperators Matrix.Norms.L2Operator

open MathlibExt.Analysis.CStarAlgebra.KadisonSinger


namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.MSS

noncomputable section

universe u

def supportSize : Fin 1 → ℕ := fun _ ↦ 2

def probability : (i : Fin 1) → Fin (supportSize i) → ℝ :=
  fun _ ↦ ![1 / 2, 1 / 2]

def randomVector : (i : Fin 1) → Fin (supportSize i) → Fin 1 → ℂ :=
  fun _ ↦ ![![1], ![-1]]

end
end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.MSS
