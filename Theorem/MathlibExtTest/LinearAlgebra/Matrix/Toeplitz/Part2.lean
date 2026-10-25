/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/Toeplitz.lean -/


import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Def.LinearAlgebra.Matrix.Toeplitz
import Lemma.Matrix.Toeplitz
import Def.MathlibExtTest.LinearAlgebra.Matrix.Toeplitz
open MetaMathlibExt


example : ¬ IsToeplitzMatrix nontoep3 := by
  rintro ⟨c, hc⟩
  have h00 := hc ⟨0, by omega⟩ ⟨0, by omega⟩
  have h11 := hc ⟨1, by omega⟩ ⟨1, by omega⟩
  simp [nontoep3] at h00 h11
  have hcontra : (1 : ℝ) = 5 := h00.trans h11.symm
  norm_num at hcontra

