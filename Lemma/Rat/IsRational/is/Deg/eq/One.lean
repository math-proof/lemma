import Mathlib
import sympy.Basic
import Def.AlgebraicCurve_PlaceEvaluation
import Lemma.Int.P2MUtil

open AlgebraicCurve

/--
[AlgebraicCurve_Place_isRational_iff_deg_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_isRational_iff_deg_eq_one.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {v : Place K F} :
-- imply
  v.IsRational ↔ v.deg = 1 := by
-- proof
  constructor
    · intro hv
      have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
        ⟨v.algebraMap_residueField_injective, hv⟩
      show Module.finrank K v.ResidueField = 1
      rw [← Module.finrank_self K]
      exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm
    · intro h x
      have hbot : (⊥ : Subalgebra K v.ResidueField) = ⊤ :=
        Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr h
      have hx : x ∈ (⊥ : Subalgebra K v.ResidueField) := by
        rw [hbot]
        exact Algebra.mem_top
      exact Algebra.mem_bot.mp hx


-- created on 2026-10-23
