/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Lie/Ado.lean -/


import Theorem.Algebra.Lie.Ado.Part5
import Lemma.Int.Lie.Ado
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Rat.Defs


namespace MathlibExtTest.Algebra.Lie.Ado

attribute [local instance 100] LieRing.ofAssociativeRing

-- Ado's representation detects a nonzero vector in a two-dimensional abelian Lie algebra.
example : ∃ (n : ℕ) (ρ : (Fin 2 → ℚ) →ₗ⁅ℚ⁆ Module.End ℚ (Fin n → ℚ)),
    ρ (fun i => if i = 0 then 1 else 0) ≠ 0 := by
  obtain ⟨n, ρ, hρ⟩ :=
    MathlibExt.Algebra.Lie.LandmarkWanted.ado (K := ℚ) (L := Fin 2 → ℚ)
  refine ⟨n, ρ, ?_⟩
  intro hzero
  have heq : (fun i : Fin 2 => if i = 0 then (1 : ℚ) else 0) = 0 :=
    hρ (hzero.trans (map_zero ρ).symm)
  have := congrFun heq 0
  simp at this

end MathlibExtTest.Algebra.Lie.Ado
