module
public import Def.Analysis.CStarAlgebra.KadisonSinger.MSS
public import Theorem.Real.CStarAlgebra.KadisonSinger.MSS
open scoped BigOperators Matrix.Norms.L2Operator
open MathlibExt.Analysis.CStarAlgebra.KadisonSinger


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger/MSS.lean -/
namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.MSS

noncomputable section

universe u

-- The proved MSS bound is available at every matrix-index universe.
example : FiniteMSSBound.{u} := finiteMSSBound

end
end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.MSS
