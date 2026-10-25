/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/JordanLinearGroups.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional


section jlBridge
end jlBridge
section jlTrick
end jlTrick
namespace MathlibExt.GroupTheory.JordanLinearGroupsWanted

open scoped commutatorElement Matrix.Norms.Elementwise

section jlDescent

/-- Iterated commutator sequence: `seq 0 = y`, `seq (k+1) = [x, seq k]`. -/
def jlSeq (n : ℕ) (x y : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    ℕ → Matrix.GeneralLinearGroup (Fin n) ℂ
  | 0 => y
  | k + 1 => ⁅x, jlSeq n x y k⁆

end jlDescent

section jlCore

/-- The near-identity set: elements of `G` within `1 / 4` of `1`. -/
def jlNearOneSet (n : ℕ)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ)) :
    Set (Matrix.GeneralLinearGroup (Fin n) ℂ) :=
  {g | g ∈ G ∧ ‖((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ) - 1‖ < 1 / 4}

end jlCore
end MathlibExt.GroupTheory.JordanLinearGroupsWanted
