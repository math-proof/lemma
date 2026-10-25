/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger/Paving.lean -/

import Def.Analysis.CStarAlgebra.KadisonSinger.Paving
import Lemma.Complex.CStarAlgebra.KadisonSinger.Paving
import Theorem.MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

open MathlibExt.Analysis.CStarAlgebra.KadisonSinger


namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving

noncomputable section

universe v

def unitFrame : Fin 1 → Fin 1 → ℂ := fun _ _ ↦ 1

def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

end
end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving
