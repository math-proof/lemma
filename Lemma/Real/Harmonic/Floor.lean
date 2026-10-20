import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Harmonic.Floor
open Asymptotics Filter
open Real


/--
[isBigO_harmonic_floor_sub_log_sub_eulerMascheroniConstant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Harmonic/Floor.lean)
-/
@[path]
private lemma isBigO_harmonic_floor_sub_log_sub_eulerMascheroniConstant_eq
  :
-- imply
  (fun x : ℝ => (harmonic ⌊x⌋₊ : ℝ) - Real.log x - Real.eulerMascheroniConstant)
    =O[atTop] (fun x : ℝ => x⁻¹) := by
-- proof
  apply Real.isBigO_harmonic_floor_sub_log_sub_eulerMascheroniConstant


-- created on 2026-10-20
