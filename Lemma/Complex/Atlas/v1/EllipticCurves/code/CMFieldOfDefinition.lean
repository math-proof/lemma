import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.EllipticCurves.code.CMFieldOfDefinition
open Matrix.SpecialLinearGroup Matrix CongruenceSubgroup CMFieldOfDefinition
open scoped MatrixGroups


namespace CMFieldOfDefinition

/--
[Gamma_le_Gamma1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMFieldOfDefinition.lean)
-/
@[path]
lemma Gamma_le_Gamma1
  {N : ℕ} :
-- imply
  Gamma N ≤ Gamma1 N := by
-- proof
  intro γ hγ
  rw [Gamma_mem] at hγ
  rw [Gamma1_mem]
  exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩

end CMFieldOfDefinition


-- created on 2026-10-23
