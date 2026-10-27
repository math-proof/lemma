import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc_binomsplit
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc_binomSplit_scalar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_binomsplit.lean)
-/
@[path]
private lemma gc_binomSplit_scalar_eq
  {X : ℝ}
  {a b : ℕ} :
-- imply
  X ^ a / (Nat.factorial a) * (X ^ b / (Nat.factorial b)) = X ^ (a + b) / (Nat.factorial (a + b)) * (Nat.choose (a + b) a : ℝ) := by
-- proof
  apply StatMech.Walls.gc_binomSplit_scalar X a b

/--
[gc_binomSplit_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_binomsplit.lean)
-/
@[path]
private lemma gc_binomSplit_edge_eq
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m n : Current V}
  {e : Sym2 V}
-- given
  (hn : n e ≤ m e) :
-- imply
  (β * J e) ^ (n e) / (Nat.factorial (n e)) * ((β * J e) ^ (m e - n e) / (Nat.factorial (m e - n e))) = (β * J e) ^ (m e) / (Nat.factorial (m e)) * (Nat.choose (m e) (n e) : ℝ) := by
-- proof
  apply StatMech.Walls.gc_binomSplit_edge β J m n e hn

/--
[gc_binomSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_binomsplit.lean)
-/
@[path]
private lemma gc_binomSplit_eq
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m n : Current V}
-- given
  (hn : n ≤ m) :
-- imply
  weight G β J n * weight G β J (fun e => m e - n e) = weight G β J m * (∏ e ∈ G.edgeFinset, (Nat.choose (m e) (n e) : ℝ)) := by
-- proof
  apply StatMech.Walls.gc_binomSplit G β J m n hn

/--
[gc_binomSplit_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_binomsplit.lean)
-/
@[path]
private lemma gc_binomSplit_two_eq
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {n₁ n₂ : Current V} :
-- imply
  weight G β J n₁ * weight G β J n₂ = weight G β J (fun e => n₁ e + n₂ e) * (∏ e ∈ G.edgeFinset, (Nat.choose (n₁ e + n₂ e) (n₁ e) : ℝ)) := by
-- proof
  apply StatMech.Walls.gc_binomSplit_two G β J n₁ n₂


-- created on 2026-10-23
