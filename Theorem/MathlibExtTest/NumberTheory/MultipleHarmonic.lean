/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleHarmonic.lean -/

import Def.NumberTheory.MultipleHarmonic
open MetaMathlibExt


example : multipleHarmonic 5 0 0 = 1 := by decide

example : multipleHarmonic 5 1 2 = 0 := by decide

example : multipleHarmonic 5 2 1 = 4 := by
  have h : (Finset.Icc 1 2).powersetCard 1 = {{1}, {2}} := by decide
  rw [multipleHarmonic, h, Finset.sum_pair (by decide)]
  simp only [Finset.prod_singleton]
  have h1 : ((1 : ℕ) : ZMod 5)⁻¹ = 1 := by simp
  have h2 : (2 : ZMod 5) * 3 = 1 := by decide
  have hinv0 : (2 : ZMod 5)⁻¹ = 3 := ZMod.inv_eq_of_mul_eq_one 5 2 3 h2
  have hinv : ((2 : ℕ) : ZMod 5)⁻¹ = 3 := by simpa using hinv0
  rw [h1, hinv]
  decide

