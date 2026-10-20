import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
  {d1 d2 : Domino}
  {k : ℕ}
-- given
  (h1_1 : d1.cell1.1 ≥ k + 1)
  (h1_2 : d1.cell2.1 ≥ k + 1)
  (h2_1 : d2.cell1.1 ≥ k + 1)
  (h2_2 : d2.cell2.1 ≥ k + 1)
  (heq : d1.shiftNeg k h1_1 h1_2 = d2.shiftNeg k h2_1 h2_2) :
-- imply
  d1 = d2 := by
-- proof
  have h1 := congrArg (·.cell1) heq
  have h2 := congrArg (·.cell2) heq
  unfold shiftNeg at h1 h2
  simp only [Prod.mk.injEq] at h1 h2
  have hc1_1 : d1.cell1.1 = d2.cell1.1 := by omega
  have hc2_1 : d1.cell2.1 = d2.cell2.1 := by omega
  cases d1
  cases d2
  simp only [Domino.mk.injEq]
  simp only at hc1_1 hc2_1 h1 h2
  constructor <;> ext <;> simp_all


-- created on 2026-10-20
