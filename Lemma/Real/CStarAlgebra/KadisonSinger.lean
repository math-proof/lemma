import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.CStarAlgebra.KadisonSinger
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open MathlibExt.Analysis.CStarAlgebra.KadisonSinger
open MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted


/--
[kadison_singer_paving](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger.lean)
-/
@[path]
private lemma kadison_singer_paving_eq
  {ε : ℝ}
-- given
  (hε : 0 < ε) :
-- imply
  ∃ (r : ℕ), 0 < r ∧
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
    A.IsHermitian → (∀ i : Fin n, A i i = 0) → ‖A‖ ≤ 1 →
    ∃ (c : Fin n → Fin r), ∀ (j : Fin r),
    ‖pavingProj n r c j * A * pavingProj n r c j‖ ≤ ε := by
-- proof
  apply MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted.kadison_singer_paving ε hε


-- created on 2026-10-20
