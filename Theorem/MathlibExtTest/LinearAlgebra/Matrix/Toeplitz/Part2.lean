module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order
public import Def.LinearAlgebra.Matrix.Toeplitz
public import Theorem.Matrix.Toeplitz
public import Def.MathlibExtTest.LinearAlgebra.Matrix.Toeplitz
open MetaMathlibExt


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/Toeplitz.lean -/

example : ¬ IsToeplitzMatrix nontoep3 := by
  rintro ⟨c, hc⟩
  have h00 := hc ⟨0, by omega⟩ ⟨0, by omega⟩
  have h11 := hc ⟨1, by omega⟩ ⟨1, by omega⟩
  simp [nontoep3] at h00 h11
  have hcontra : (1 : ℝ) = 5 := h00.trans h11.symm
  norm_num at hcontra

