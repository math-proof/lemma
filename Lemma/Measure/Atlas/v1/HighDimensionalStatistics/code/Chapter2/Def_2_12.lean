import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Def_2_12
open Finset Matrix BigOperators Rigollet


namespace Rigollet

/--
[l0norm_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Def_2_12.lean)
-/
@[path]
lemma l0norm_eq
  {d : ℕ}
  {θ : Fin d → ℝ} :
-- imply
  l0norm θ = (Finset.univ.filter (fun j => θ j ≠ 0)).card :=
-- proof
  rfl

end Rigollet

namespace Rigollet

/--
[l1norm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Def_2_12.lean)
-/
@[path]
lemma l1norm_nonneg
  {d : ℕ}
  {θ : Fin d → ℝ} :
-- imply
  0 ≤ l1norm θ :=
-- proof
  Finset.sum_nonneg (fun j _ => abs_nonneg (θ j))

end Rigollet

namespace Rigollet

/--
[l0norm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Def_2_12.lean)
-/
@[path]
lemma l0norm_zero
  {d : ℕ} :
-- imply
  l0norm (0 : Fin d → ℝ) = 0 := by
-- proof
  simp [l0norm]

end Rigollet

namespace Rigollet

/--
[sqL2norm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Def_2_12.lean)
-/
@[path]
lemma sqL2norm_nonneg
  {n : ℕ}
  {v : Fin n → ℝ} :
-- imply
  0 ≤ sqL2norm v :=
-- proof
  Finset.sum_nonneg (fun i _ => sq_nonneg (v i))

end Rigollet


-- created on 2026-10-23
