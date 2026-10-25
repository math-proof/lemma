import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessFull.Part3
open MeasureTheory Set Filter Topology StatMech StatMech.FK


/--
[dlr_sandwich_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessFull.lean)
-/
@[path]
private lemma dlr_sandwich_unique_eq
  [MeasurableSpace Ω]
  {free wired phi : Measure Ω}
  {A : Set Ω}
-- given
  (hsand : free.real A ≤ phi.real A ∧ phi.real A ≤ wired.real A)
  (hfw : free.real A = wired.real A) :
-- imply
  phi.real A = free.real A ∧ phi.real A = wired.real A := by
-- proof
  apply StatMech.FK.dlr_sandwich_unique hsand hfw

/--
[sandwich_eq_of_free_eq_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessFull.lean)
-/
@[path]
private lemma sandwich_eq_of_free_eq_wired_eq
  [MeasurableSpace Ω]
  {free wired phi : Measure Ω}
  {P : Set Ω → Prop}
-- given
  (hsand : ∀ A, P A → free.real A ≤ phi.real A ∧ phi.real A ≤ wired.real A)
  (hfw : ∀ A, P A → free.real A = wired.real A) :
-- imply
  ∀ A, P A → phi.real A = free.real A ∧ phi.real A = wired.real A := by
-- proof
  apply StatMech.FK.sandwich_eq_of_free_eq_wired hsand hfw

/--
[countable_density_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessFull.lean)
-/
@[path]
private lemma countable_density_ne_eq
  [MeasurableSpace Ω]
  {a b : ℝ → ℝ}
-- given
  (hb : Monotone b)
  (heq_at_cont : ∀ p, ContinuousAt b p → a p = b p) :
-- imply
  {p : ℝ | a p ≠ b p}.Countable := by
-- proof
  apply StatMech.FK.countable_density_ne hb heq_at_cont

/--
[fk_uniqueness_off_countable_abstract](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessFull.lean)
-/
@[path]
private lemma fk_uniqueness_off_countable_abstract_eq
  [MeasurableSpace Ω]
  {free wired : ℝ → Measure Ω}
  {a b : ℝ → ℝ}
-- given
  (P : Set Ω → Prop)
  (hb : Monotone b)
  (heq_at_cont : ∀ p, ContinuousAt b p → a p = b p)
  (hcrit : ∀ p, a p = b p → ∀ A, P A → (free p).real A = (wired p).real A) :
-- imply
  ∃ S : Set ℝ, S.Countable ∧ ∀ p ∉ S, ∀ phi : Measure Ω, (∀ A, P A → (free p).real A ≤ phi.real A ∧ phi.real A ≤ (wired p).real A) → ∀ A, P A → phi.real A = (free p).real A ∧ phi.real A = (wired p).real A := by
-- proof
  apply StatMech.FK.fk_uniqueness_off_countable_abstract free wired P a b hb heq_at_cont hcrit

/--
[isIncreasing_fkEdgeOpenEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessFull.lean)
-/
@[path]
private lemma isIncreasing_fkEdgeOpenEvent_eq
  {e : E} :
-- imply
  IsIncreasing (fkEdgeOpenEvent e) := by
-- proof
  apply StatMech.FK.isIncreasing_fkEdgeOpenEvent e

/--
[wiredEdgeDensity_monotone_of_pressure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessFull.lean)
-/
@[path]
private lemma wiredEdgeDensity_monotone_of_pressure_eq
  {d : ℕ}
  {q : ℝ}
  {e : Sym2 (Site d)}
  {g : ℝ → ℝ}
-- given
  (hg : ConvexOn ℝ univ g)
  (hb_eq : ∀ p, wiredEdgeDensity d q e p = pressureRightDeriv g p) :
-- imply
  Monotone (wiredEdgeDensity d q e) := by
-- proof
  apply StatMech.FK.wiredEdgeDensity_monotone_of_pressure d q e hg hb_eq

/--
[fk_uniqueness_off_countable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessFull.lean)
-/
@[path]
private lemma fk_uniqueness_off_countable_eq
  {d : ℕ}
  {q : ℝ}
  {e : Sym2 (Site d)}
-- given
  (hb : Monotone (wiredEdgeDensity d q e))
  (heq_at_cont : ∀ p, ContinuousAt (wiredEdgeDensity d q e) p → freeEdgeDensity d q e p = wiredEdgeDensity d q e p)
  (hcrit : ∀ p, freeEdgeDensity d q e p = wiredEdgeDensity d q e p → ∀ A : Set (ConfigSpace (Sym2 (Site d))), IsIncreasing A → ∀ {hp : 0 < p} {hp1 : p < 1} {hq : 0 < q}, (freeInfiniteVolume d hp hp1 hq : Measure _).real A = (wiredInfiniteVolume d hp hp1 hq : Measure _).real A) :
-- imply
  ∀ {hq : 0 < q}, ∃ S : Set ℝ, S.Countable ∧ ∀ p ∉ S, ∀ (hp : 0 < p) (hp1 : p < 1) (phi : Measure (ConfigSpace (Sym2 (Site d)))), (∀ A : Set (ConfigSpace (Sym2 (Site d))), IsIncreasing A → (freeInfiniteVolume d hp hp1 hq : Measure _).real A ≤ phi.real A ∧ phi.real A ≤ (wiredInfiniteVolume d hp hp1 hq : Measure _).real A) → ∀ A : Set (ConfigSpace (Sym2 (Site d))), IsIncreasing A → phi.real A = (freeInfiniteVolume d hp hp1 hq : Measure _).real A ∧ phi.real A = (wiredInfiniteVolume d hp hp1 hq : Measure _).real A := by
-- proof
  apply StatMech.FK.fk_uniqueness_off_countable d q e hb heq_at_cont hcrit


-- created on 2026-10-23
