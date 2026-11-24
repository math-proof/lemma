module
public import Def.Analysis.CStarAlgebra.KadisonSinger
public import Theorem.Real.CStarAlgebra.KadisonSinger
open scoped Matrix.Norms.L2Operator
open MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger.lean -/
namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger

noncomputable section

def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

end
end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger
