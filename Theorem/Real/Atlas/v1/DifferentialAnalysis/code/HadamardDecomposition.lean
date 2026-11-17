module

public import Mathlib
public import Def.v1.Atlas.DifferentialAnalysis.code.HadamardDecomposition

public section

open HadamardDecomposition
open scoped SchwartzMap


namespace HadamardDecomposition

/--
[coordFun_eq_coordCLM](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HadamardDecomposition.lean)
-/
public theorem coordFun_eq_coordCLM
  {n : ℕ}
  {j : Fin n} :
-- imply
  coordFun n j = coordCLM n j := by
-- proof
  ext x; simp [coordFun, coordCLM, EuclideanSpace.proj]

end HadamardDecomposition

namespace HadamardDecomposition

/--
[coordFun_hasTemperateGrowth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HadamardDecomposition.lean)
-/
public theorem coordFun_hasTemperateGrowth
  {n : ℕ}
  {j : Fin n} :
-- imply
  Function.HasTemperateGrowth (coordFun n j) := by
-- proof
  rw [coordFun_eq_coordCLM]; exact ContinuousLinearMap.hasTemperateGrowth _

end HadamardDecomposition


-- created on 2026-10-23
