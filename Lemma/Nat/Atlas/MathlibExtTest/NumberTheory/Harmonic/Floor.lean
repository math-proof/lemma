import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.NumberTheory.Harmonic.Floor
open Asymptotics Filter Real Topology


/--
[tendsto_centered_floor_harmonic_error_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Harmonic/Floor.lean)
-/
@[path]
lemma tendsto_centered_floor_harmonic_error_atTop
-- imply
  Filter.Tendsto (fun x : ℝ => (harmonic ⌊x⌋₊ : ℝ) - Real.log x - eulerMascheroniConstant) Filter.atTop (nhds 0) :=
-- proof
  Real.isBigO_harmonic_floor_sub_log_sub_eulerMascheroniConstant.trans_tendsto
    tendsto_inv_atTop_zero


-- created on 2026-10-23
