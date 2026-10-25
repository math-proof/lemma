import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.fc_scalarengine
open Set Filter Topology StatMech StatMech.Walls


/--
[fc_almostMono_converges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_scalarengine.lean)
-/
@[path]
private lemma fc_almostMono_converges_eq
  {a δ : ℕ → ℝ}
-- given
  (hδ : ∀ n, 0 ≤ δ n)
  (hsum : Summable δ)
  (hmono : ∀ n, a n - δ n ≤ a (n + 1))
  (hbdd : BddAbove (range a)) :
-- imply
  ∃ L, Tendsto a atTop (𝓝 L) := by
-- proof
  apply StatMech.Walls.fc_almostMono_converges a δ hδ hsum hmono hbdd

/--
[fc_almostMono_converges_subadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_scalarengine.lean)
-/
@[path]
private lemma fc_almostMono_converges_subadditive_eq
  {a : ℕ → ℝ}
-- given
  (hmono : ∀ n, a n ≤ a (n + 1))
  (hbdd : BddAbove (range a)) :
-- imply
  ∃ L, Tendsto a atTop (𝓝 L) := by
-- proof
  apply StatMech.Walls.fc_almostMono_converges_subadditive a hmono hbdd

/--
[fc_natLog_tendsto_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_scalarengine.lean)
-/
@[path]
private lemma fc_natLog_tendsto_atTop_eq :
-- imply
  Tendsto (fun n => Nat.log 2 n) atTop atTop := by
-- proof
  apply StatMech.Walls.fc_natLog_tendsto_atTop

/--
[fc_full_from_dyadic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_scalarengine.lean)
-/
@[path]
private lemma fc_full_from_dyadic_eq
  {a : ℕ → ℝ}
  {L : ℝ}
  {osc : ℕ → ℝ}
-- given
  (hdy : Tendsto (fun j => a (2 ^ j)) atTop (𝓝 L))
  (hosc : Tendsto osc atTop (𝓝 0))
  (hsand : ∀ n, 1 ≤ n → |a n - a (2 ^ (Nat.log 2 n))| ≤ osc (Nat.log 2 n)) :
-- imply
  Tendsto a atTop (𝓝 L) := by
-- proof
  apply StatMech.Walls.fc_full_from_dyadic a L hdy osc hosc hsand

/--
[fc_scalar_converges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_scalarengine.lean)
-/
@[path]
private lemma fc_scalar_converges_eq
  {g δ osc : ℕ → ℝ}
-- given
  (hδ : ∀ j, 0 ≤ δ j)
  (hsum : Summable δ)
  (hdymono : ∀ j, g (2 ^ j) - δ j ≤ g (2 ^ (j + 1)))
  (hbdd : BddAbove (range (fun j => g (2 ^ j))))
  (hosc : Tendsto osc atTop (𝓝 0))
  (hsand : ∀ n, 1 ≤ n → |g n - g (2 ^ (Nat.log 2 n))| ≤ osc (Nat.log 2 n)) :
-- imply
  ∃ L, Tendsto g atTop (𝓝 L) := by
-- proof
  apply StatMech.Walls.fc_scalar_converges g δ osc hδ hsum hdymono hbdd hosc hsand

/--
[fc_scalar_converges_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_scalarengine.lean)
-/
@[path]
private lemma fc_scalar_converges_satisfiable_eq :
-- imply
  ∃ (g δ osc : ℕ → ℝ), (∀ j, 0 ≤ δ j) ∧ Summable δ ∧ (∀ j, g (2 ^ j) - δ j ≤ g (2 ^ (j + 1))) ∧ BddAbove (range (fun j => g (2 ^ j))) ∧ Tendsto osc atTop (𝓝 0) ∧ (∀ n, 1 ≤ n → |g n - g (2 ^ (Nat.log 2 n))| ≤ osc (Nat.log 2 n)) := by
-- proof
  apply StatMech.Walls.fc_scalar_converges_satisfiable


-- created on 2026-10-23
