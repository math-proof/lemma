/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/BasicHypergeometric.lean -/


import sympy.atlas.Analysis.SpecialFunctions.BasicHypergeometric
import Mathlib.Tactic.NormNum


namespace MetaMathlibExt.BasicHypergeometric

open Finset

example (q : ℂ) : basicHypergeometricCoefficient Fin.elim0 Fin.elim0 q 0 = 1 := by simp

example (a : Fin 1 → ℂ) (q : ℂ) (n : ℕ) :
    PowerSeries.coeff n (basicHypergeometricSeries a Fin.elim0 q) =
      basicHypergeometricCoefficient a Fin.elim0 q n := by
  simp

example (a : ℂ) (q : ℂ) :
    basicHypergeometricCoefficient (fun _ : Fin 1 => a) Fin.elim0 q 1 =
      (1 - a) / (1 - q) := by
  rw [basicHypergeometricCoefficient_phi_succ]
  simp

example (a b q : ℂ) :
    basicHypergeometricCoefficient (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) q 1 =
      -((1 - a) / ((1 - q) * (1 - b))) := by
  simp [basicHypergeometricCoefficient]

/-- This example detects an accidental use of truncated natural-number subtraction in the
normalization exponent. -/
example :
    basicHypergeometricCoefficient (fun _ : Fin 2 => (0 : ℂ)) Fin.elim0 (2 : ℂ) 1 = 1 := by
  simp [basicHypergeometricCoefficient]
  norm_num

/-- This example checks that the triangular q-power lies inside the base raised to the
normalization exponent. -/
example :
    basicHypergeometricCoefficient Fin.elim0 (fun _ : Fin 1 => (0 : ℂ)) (2 : ℂ) 2 =
      (4 : ℂ) / 3 := by
  norm_num [basicHypergeometricCoefficient, prod_range_succ]

end MetaMathlibExt.BasicHypergeometric
