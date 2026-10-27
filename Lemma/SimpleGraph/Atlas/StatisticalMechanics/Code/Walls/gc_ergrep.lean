import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc_ergrep
open Finset SimpleGraph StatMech StatMech.Walls


/--
[gc_ergrep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_ergrep.lean)
-/
@[path]
private lemma gc_ergrep_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {A : Finset V} :
-- imply
  isingExpectation G β 0 (spinProd A) = currentSum G β (fun _ => 1) A / currentSum G β (fun _ => 1) ∅ := by
-- proof
  apply StatMech.Walls.gc_ergrep G β A

/--
[gc_ergrep_currentSum_eq_betaWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_ergrep.lean)
-/
@[path]
private lemma gc_ergrep_currentSum_eq_betaWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {A : Finset V} :
-- imply
  currentSum G β (fun _ => 1) A = ∑' m : ↥G.edgeFinset → ℕ, if sources G (ofEdgeFun G m) = A then (∏ e : ↥G.edgeFinset, β ^ (m e) / (Nat.factorial (m e))) else 0 := by
-- proof
  apply StatMech.Walls.gc_ergrep_currentSum_eq_betaWeight G β A

/--
[gc_ergrep_betaWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_ergrep.lean)
-/
@[path]
private lemma gc_ergrep_betaWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {A : Finset V} :
-- imply
  isingExpectation G β 0 (spinProd A) = (∑' m : ↥G.edgeFinset → ℕ, if sources G (ofEdgeFun G m) = A then (∏ e : ↥G.edgeFinset, β ^ (m e) / (Nat.factorial (m e))) else 0) / (∑' m : ↥G.edgeFinset → ℕ, if sources G (ofEdgeFun G m) = ∅ then (∏ e : ↥G.edgeFinset, β ^ (m e) / (Nat.factorial (m e))) else 0) := by
-- proof
  apply StatMech.Walls.gc_ergrep_betaWeight G β A

/--
[gc_ergrep_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_ergrep.lean)
-/
@[path]
private lemma gc_ergrep_general_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  expectationJ G β J A = currentSum G β J A / currentSum G β J ∅ := by
-- proof
  apply StatMech.Walls.gc_ergrep_general G β J A

/--
[gc_ergrep_denom_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_ergrep.lean)
-/
@[path]
private lemma gc_ergrep_denom_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ} :
-- imply
  0 < currentSum G β (fun _ => 1) ∅ := by
-- proof
  apply StatMech.Walls.gc_ergrep_denom_pos G β


-- created on 2026-10-23
