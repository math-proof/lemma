import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part4
open Module Fintype


namespace Definitions
end Definitions

/--
[lie_H_E_C](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean)
-/
@[path]
private lemma lie_H_E_C_eq :
-- imply
  (Bracket.bracket basisH_C basisE_C) = 2 • basisE_C := by
-- proof
  apply lie_H_E_C

/--
[lie_H_F_C](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean)
-/
@[path]
private lemma lie_H_F_C_eq :
-- imply
  (Bracket.bracket basisH_C basisF_C) = (-2) • basisF_C := by
-- proof
  apply lie_H_F_C

/--
[lie_E_F_C](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean)
-/
@[path]
private lemma lie_E_F_C_eq :
-- imply
  (Bracket.bracket basisE_C basisF_C) = basisH_C := by
-- proof
  apply lie_E_F_C

/--
[finrank_sl2C](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean)
-/
@[path]
private lemma finrank_sl2C_eq :
-- imply
  Module.finrank ℂ sl2C = 3 := by
-- proof
  apply finrank_sl2C

/--
[finrank_sl2R](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean)
-/
@[path]
private lemma finrank_sl2R_eq :
-- imply
  Module.finrank ℝ sl2R = 3 := by
-- proof
  apply finrank_sl2R

/--
[basisH_C_mem_sl2C](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean)
-/
@[path]
private lemma basisH_C_mem_sl2C_eq :
-- imply
  basisH_C ∈ sl2C := by
-- proof
  apply basisH_C_mem_sl2C

/--
[basisE_C_mem_sl2C](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean)
-/
@[path]
private lemma basisE_C_mem_sl2C_eq :
-- imply
  basisE_C ∈ sl2C := by
-- proof
  apply basisE_C_mem_sl2C

/--
[basisF_C_mem_sl2C](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean)
-/
@[path]
private lemma basisF_C_mem_sl2C_eq :
-- imply
  basisF_C ∈ sl2C := by
-- proof
  apply basisF_C_mem_sl2C

/--
[basisH_C_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean)
-/
@[path]
private lemma basisH_C_ne_zero_eq :
-- imply
  basisH_C ≠ 0 := by
-- proof
  apply basisH_C_ne_zero

/--
[sl2H_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean)
-/
@[path]
private lemma sl2H_ne_zero_eq :
-- imply
  sl2H ≠ 0 := by
-- proof
  apply sl2H_ne_zero

/--
[sl2_lie_EF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean)
-/
@[path]
private lemma sl2_lie_EF_eq :
-- imply
  (Bracket.bracket sl2E sl2F) = sl2H := by
-- proof
  apply sl2_lie_EF

/--
[sl2_lie_HE](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean)
-/
@[path]
private lemma sl2_lie_HE_eq :
-- imply
  (Bracket.bracket sl2H sl2E) = 2 • sl2E := by
-- proof
  apply sl2_lie_HE

/--
[sl2_lie_HF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean)
-/
@[path]
private lemma sl2_lie_HF_eq :
-- imply
  (Bracket.bracket sl2H sl2F) = -(2 • sl2F) := by
-- proof
  apply sl2_lie_HF


-- created on 2026-10-24
