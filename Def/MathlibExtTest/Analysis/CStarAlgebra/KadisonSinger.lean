/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger.lean -/

import Def.Analysis.CStarAlgebra.KadisonSinger
import Lemma.Real.CStarAlgebra.KadisonSinger
open scoped Matrix.Norms.L2Operator

open MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted


namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger

noncomputable section

def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

end
end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger
