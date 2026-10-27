import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
open MeasureTheory Set StatMech StatMech.Percolation


/--
[mem_crossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecay.lean)
-/
@[path]
private lemma mem_crossingEvent_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  ω ∈ crossingEvent d n ↔ ∃ v, Connected d ω (origin d) v ∧ v ∉ box d (n - 1) := by
-- proof
  apply StatMech.Percolation.mem_crossingEvent

/--
[crossingEvent_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecay.lean)
-/
@[path]
private lemma crossingEvent_antitone_eq
  {d : ℕ}
  {m n : ℕ}
-- given
  (hmn : m ≤ n) :
-- imply
  crossingEvent d n ⊆ crossingEvent d m := by
-- proof
  apply StatMech.Percolation.crossingEvent_antitone m n hmn

/--
[crossProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecay.lean)
-/
@[path]
private lemma crossProb_nonneg_eq
  {d : ℕ}
  {d : ℕ}
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  0 ≤ crossProb d p hp n := by
-- proof
  apply StatMech.Percolation.crossProb_nonneg d p hp n

/--
[crossProb_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecay.lean)
-/
@[path]
private lemma crossProb_le_one_eq
  {d : ℕ}
  {d : ℕ}
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  crossProb d p hp n ≤ 1 := by
-- proof
  apply StatMech.Percolation.crossProb_le_one d p hp n

/--
[crossProb_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecay.lean)
-/
@[path]
private lemma crossProb_antitone_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  Antitone (crossProb d p hp) := by
-- proof
  apply StatMech.Percolation.crossProb_antitone d p hp

/--
[recursion_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecay.lean)
-/
@[path]
private lemma recursion_le_pow_eq
  {d : ℕ}
  {f : ℕ → ℝ}
  {r : ℝ}
-- given
  (hf0 : f 0 ≤ 1)
  (hr : 0 ≤ r)
  (hrec : ∀ k, f (k + 1) ≤ r * f k) :
-- imply
  ∀ k, f k ≤ r ^ k := by
-- proof
  apply StatMech.Percolation.recursion_le_pow hf0 hr hrec

/--
[geometric_subseq_antitone_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecay.lean)
-/
@[path]
private lemma geometric_subseq_antitone_decay_eq
  {d : ℕ}
  {f : ℕ → ℝ}
  {r : ℝ}
  {L : ℕ}
-- given
  (hL : 1 ≤ L)
  (hr0 : 0 < r)
  (hr1 : r < 1)
  (hanti : Antitone f)
  (hsub : ∀ k, f (k * L) ≤ r ^ k) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ n, f n ≤ C * Real.exp (-c * n) := by
-- proof
  apply StatMech.Percolation.geometric_subseq_antitone_decay hL hr0 hr1 hanti hsub

/--
[step_with_pos_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecay.lean)
-/
@[path]
private lemma step_with_pos_ratio_eq
  {d : ℕ}
  {f : ℕ → ℝ}
  {r₀ : ℝ}
-- given
  (hfnn : ∀ k, 0 ≤ f k)
  (hr1 : r₀ < 1)
  (hrec : ∀ k, f (k + 1) ≤ r₀ * f k) :
-- imply
  ∃ r, 0 < r ∧ r < 1 ∧ ∀ k, f (k + 1) ≤ r * f k := by
-- proof
  apply StatMech.Percolation.step_with_pos_ratio hfnn hr1 hrec

/--
[subcritical_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecay.lean)
-/
@[path]
private lemma subcritical_decay_eq
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
  apply StatMech.Percolation.subcritical_decay p hp S hS0 hphi L hL hstep


-- created on 2026-10-23
