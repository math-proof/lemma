import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
open MeasureTheory Set StatMech StatMech.Percolation


/--
[shift_eq_piCongrLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecayFull.lean)
-/
@[path]
private lemma shift_eq_piCongrLeft_eq
  [Group G]
  [MulAction G E]
  {g : G} :
-- imply
  (shift g : ConfigSpace E → ConfigSpace E) = ⇑(Equiv.piCongrLeft (fun _ : E => Bool) (MulAction.toPerm g)) := by
-- proof
  apply StatMech.Percolation.shift_eq_piCongrLeft g

/--
[bernoulli_translationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecayFull.lean)
-/
@[path]
private lemma bernoulli_translationInvariant_eq
  [Group G]
  [MulAction G E]
  [Countable E]
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  IsTranslationInvariant (G := G) (bernoulliProductMeasure (E := E) p hp) := by
-- proof
  apply StatMech.Percolation.bernoulli_translationInvariant p hp

/--
[mem_crossingEventFrom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecayFull.lean)
-/
@[path]
private lemma mem_crossingEventFrom_eq
  {d : ℕ}
  {y : Site d}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  ω ∈ crossingEventFrom d y n ↔ ∃ v, Connected d ω y v ∧ v ∉ box d (n - 1) := by
-- proof
  apply StatMech.Percolation.mem_crossingEventFrom

/--
[crossingEventFrom_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecayFull.lean)
-/
@[path]
private lemma crossingEventFrom_origin_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  crossingEventFrom d (origin d) n = crossingEvent d n := by
-- proof
  apply StatMech.Percolation.crossingEventFrom_origin n

/--
[measurableSet_crossingEventFrom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecayFull.lean)
-/
@[path]
private lemma measurableSet_crossingEventFrom_eq
  {d : ℕ}
  {y : Site d}
  {n : ℕ} :
-- imply
  MeasurableSet (crossingEventFrom d y n) := by
-- proof
  apply StatMech.Percolation.measurableSet_crossingEventFrom y n

/--
[measurableSet_crossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecayFull.lean)
-/
@[path]
private lemma measurableSet_crossingEvent_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  MeasurableSet (crossingEvent d n) := by
-- proof
  apply StatMech.Percolation.measurableSet_crossingEvent n

/--
[crossingEventFrom_eq_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecayFull.lean)
-/
@[path]
private lemma crossingEventFrom_eq_preimage_eq
  {d : ℕ}
  {y : Site d}
  {n : ℕ} :
-- imply
  crossingEventFrom d y n = (shift (Multiplicative.ofAdd (-y)) : ConfigSpace (Sym2 (Site d)) → _) ⁻¹' {ω | ∃ v, Connected d ω (origin d) v ∧ (v + y) ∉ box d (n - 1)} := by
-- proof
  apply StatMech.Percolation.crossingEventFrom_eq_preimage y n

/--
[box_shift_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecayFull.lean)
-/
@[path]
private lemma box_shift_mem_eq
  {d : ℕ}
  {y v : Site d}
  {L m n : ℕ}
-- given
  (hy : y ∈ box d L)
  (hv : v ∈ box d (m - 1))
  (hmLn : m + L ≤ n)
  (hm : 1 ≤ m) :
-- imply
  (v + y) ∈ box d (n - 1) := by
-- proof
  apply StatMech.Percolation.box_shift_mem hy hv hmLn hm

/--
[crossProbFrom_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecayFull.lean)
-/
@[path]
private lemma crossProbFrom_le_eq
  {d : ℕ}
  {y : Site d}
  {L m n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hy : y ∈ box d L)
  (hmLn : m + L ≤ n)
  (hm : 1 ≤ m) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (crossingEventFrom d y n) ≤ crossProb d p hp m := by
-- proof
  apply StatMech.Percolation.crossProbFrom_le p hp y hy hmLn hm

/--
[subcritical_decay_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecayFull.lean)
-/
@[path]
private lemma subcritical_decay_full_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {L : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hS0 : origin d ∈ S)
  (hphi : phi d p hp S < 1)
  (hL : 1 ≤ L)
  (hstep : ∀ k, crossProb d p hp ((k + 1) * L) ≤ phi d p hp S * crossProb d p hp (k * L)) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n) := by
-- proof
  apply StatMech.Percolation.subcritical_decay_full p hp S hS0 hphi L hL hstep


-- created on 2026-10-23
