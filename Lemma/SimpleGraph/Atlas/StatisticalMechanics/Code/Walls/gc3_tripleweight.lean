import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc3_tripleweight
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc3_tripleWeight_aux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_tripleweight.lean)
-/
@[path]
private lemma gc3_tripleWeight_aux_eq
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {n₁ n₂ n₃ : Current V} :
-- imply
  weight G β J n₁ * weight G β J n₂ * weight G β J n₃ = (∏ e ∈ G.edgeFinset, ((Nat.choose (n₁ e + n₂ e + n₃ e) (n₁ e) : ℝ) * (Nat.choose (n₂ e + n₃ e) (n₂ e) : ℝ))) * weight G β J (fun e => n₁ e + n₂ e + n₃ e) := by
-- proof
  apply StatMech.Walls.gc3_tripleWeight_aux G β J n₁ n₂ n₃

/--
[gc3_tripleWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_tripleweight.lean)
-/
@[path]
private lemma gc3_tripleWeight_eq
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {n₁ n₂ n₃ : Current V}
  {m : Current V}
-- given
  (hm : m = fun e => n₁ e + n₂ e + n₃ e) :
-- imply
  weight G β J n₁ * weight G β J n₂ * weight G β J n₃ = (∏ e ∈ G.edgeFinset, ((Nat.choose (m e) (n₁ e) : ℝ) * (Nat.choose (m e - n₁ e) (n₂ e) : ℝ))) * weight G β J m := by
-- proof
  apply StatMech.Walls.gc3_tripleWeight G β J n₁ n₂ n₃ m hm


-- created on 2026-10-23
