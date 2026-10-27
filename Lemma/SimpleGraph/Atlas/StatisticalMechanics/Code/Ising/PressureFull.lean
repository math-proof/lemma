import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.PressureFull
open Finset Filter Topology StatMech StatMech.Ising


/--
[logFvZ_convexOn_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureFull.lean)
-/
@[path]
private lemma logFvZ_convexOn_beta_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (h : ℝ) :
-- imply
  ConvexOn ℝ Set.univ (fun β : ℝ => Real.log (fvZ η n B β h)) := by
-- proof
  apply StatMech.Ising.logFvZ_convexOn_beta η n B h

/--
[logFvZ_convexOn_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureFull.lean)
-/
@[path]
private lemma logFvZ_convexOn_field_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {β : ℝ} :
-- imply
  ConvexOn ℝ Set.univ (fun h : ℝ => Real.log (fvZ η n B β h)) := by
-- proof
  apply StatMech.Ising.logFvZ_convexOn_field η n B β

/--
[pressure_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureFull.lean)
-/
@[path]
private lemma pressure_full_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
-- given
  (β h : ℝ) :
-- imply
  Tendsto (fun n => logZSeq β (hamiltonian G h) n / n) atTop (𝓝 (pressure β (hamiltonian G h))) ∧ pressure β (hamiltonian G h) = Real.log (isingZ G β h) ∧ ConvexOn ℝ Set.univ (fun β' : ℝ => Real.log (isingZ G β' h)) ∧ ConvexOn ℝ Set.univ (fun h' : ℝ => Real.log (isingZ G β h')) := by
-- proof
  apply StatMech.Ising.pressure_full β h

/--
[boxPressure_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureFull.lean)
-/
@[path]
private lemma boxPressure_full_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {n : ℕ}
-- given
  (β h : ℝ)
  (hratio : Tendsto (fun m => (|β| * (((bondFinsetTouch d m) \ (bondFinsetInternal d m)).card : ℝ)) / ((boxFinset d m).card : ℝ)) atTop (𝓝 0)) :
-- imply
  ConvexOn ℝ Set.univ (fun β' : ℝ => Real.log (fvZ (plusField d) n (bondFinsetTouch d n) β' h)) ∧ ConvexOn ℝ Set.univ (fun h' : ℝ => Real.log (fvZ (plusField d) n (bondFinsetTouch d n) β h')) ∧ Tendsto (fun m => Real.log (fvZ (plusField d) m (bondFinsetTouch d m) β h) / ((boxFinset d m).card : ℝ) - Real.log (fvZ (minusField d) m (bondFinsetInternal d m) β h) / ((boxFinset d m).card : ℝ)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Ising.boxPressure_full n β h hratio

/--
[boxPressure_plus_free_same_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureFull.lean)
-/
@[path]
private lemma boxPressure_plus_free_same_limit_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
-- given
  (β h p : ℝ)
  (hratio : Tendsto (fun m => (|β| * (((bondFinsetTouch d m) \ (bondFinsetInternal d m)).card : ℝ)) / ((boxFinset d m).card : ℝ)) atTop (𝓝 0))
  (hplus : Tendsto (fun m => Real.log (fvZ (plusField d) m (bondFinsetTouch d m) β h) / ((boxFinset d m).card : ℝ)) atTop (𝓝 p)) :
-- imply
  Tendsto (fun m => Real.log (fvZ (minusField d) m (bondFinsetInternal d m) β h) / ((boxFinset d m).card : ℝ)) atTop (𝓝 p) := by
-- proof
  apply StatMech.Ising.boxPressure_plus_free_same_limit β h p hratio hplus


-- created on 2026-10-23
