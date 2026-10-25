import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc5_ergrep
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc5_currentSum_eq_sum_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ergrep.lean)
-/
@[path]
private lemma gc5_currentSum_eq_sum_weight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  Sharpness.currentSum G β J A = ∑' m : ↥G.edgeFinset → ℕ, (if Sharpness.sources G (Sharpness.ofEdgeFun G m) = A then Sharpness.weight G β J (Sharpness.ofEdgeFun G m) else 0) := by
-- proof
  apply StatMech.Walls.gc5_currentSum_eq_sum_weight G β J A

/--
[gc5_Z0_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ergrep.lean)
-/
@[path]
private lemma gc5_Z0_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ} :
-- imply
  0 < Sharpness.currentSum G β J ∅ := by
-- proof
  apply StatMech.Walls.gc5_Z0_pos G β J

/--
[gc5_Z0_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ergrep.lean)
-/
@[path]
private lemma gc5_Z0_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ} :
-- imply
  Sharpness.currentSum G β J ∅ ≠ 0 := by
-- proof
  apply StatMech.Walls.gc5_Z0_ne_zero G β J

/--
[gc5_ergRep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ergrep.lean)
-/
@[path]
private lemma gc5_ergRep_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {A : Finset V} :
-- imply
  isingExpectation G β 0 (spinProd A) = Sharpness.currentSum G β (fun _ => 1) A / Sharpness.currentSum G β (fun _ => 1) ∅ := by
-- proof
  apply StatMech.Walls.gc5_ergRep G β A

/--
[gc5_ergRep_J](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ergrep.lean)
-/
@[path]
private lemma gc5_ergRep_J_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  Sharpness.expectationJ G β J A = Sharpness.currentSum G β J A / Sharpness.currentSum G β J ∅ := by
-- proof
  apply StatMech.Walls.gc5_ergRep_J G β J A

/--
[gc5_ratio_well_defined](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ergrep.lean)
-/
@[path]
private lemma gc5_ratio_well_defined_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {A : Finset V} :
-- imply
  isingExpectation G β 0 (spinProd A) = Sharpness.currentSum G β (fun _ => 1) A / Sharpness.currentSum G β (fun _ => 1) ∅ ∧ 0 < Sharpness.currentSum G β (fun _ => 1) ∅ := by
-- proof
  apply StatMech.Walls.gc5_ratio_well_defined G β A

/--
[gc5_correlation_times_Z0_eq_numerator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ergrep.lean)
-/
@[path]
private lemma gc5_correlation_times_Z0_eq_numerator_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {A : Finset V} :
-- imply
  isingExpectation G β 0 (spinProd A) * Sharpness.currentSum G β (fun _ => 1) ∅ = Sharpness.currentSum G β (fun _ => 1) A := by
-- proof
  apply StatMech.Walls.gc5_correlation_times_Z0_eq_numerator G β A


-- created on 2026-10-23
