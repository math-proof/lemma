/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Harmonic/Floor.lean -/


import Lemma.Real.Harmonic.Floor
open Asymptotics Filter Real Topology


example :
    (fun x : ℝ => (harmonic ⌊x⌋₊ : ℝ) - Real.log x -
      eulerMascheroniConstant) =O[Filter.atTop] fun x : ℝ => x⁻¹ :=
  Real.isBigO_harmonic_floor_sub_log_sub_eulerMascheroniConstant

