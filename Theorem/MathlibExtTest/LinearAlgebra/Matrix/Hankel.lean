/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/Hankel.lean -/


import Def.LinearAlgebra.Matrix.Hankel
import Lemma.Matrix.Hankel


namespace Matrix

example {α : Type*} (s : ℕ → α) : hankel s 2 3 = s 5 := by
  rfl

example {α : Type*} (s : ℕ → α) : (hankel s)ᵀ = hankel s := by
  ext i j
  simp [add_comm]

example {α : Type*} (s : ℕ → α) :
    hankelFin 4 s (1 : Fin 4) (2 : Fin 4) = s 3 := by
  rfl

#print axioms hankel
#print axioms hankelFin

end Matrix
