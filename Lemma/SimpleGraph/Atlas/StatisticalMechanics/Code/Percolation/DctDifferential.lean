import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferential.Part4
open MeasureTheory Function Set StatMech StatMech.Percolation


/--
[mem_boxFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean)
-/
@[path]
private lemma mem_boxFinset_eq
  {d : ℕ}
  {d n : ℕ}
  {x : Site d} :
-- imply
  x ∈ boxFinset d n ↔ x ∈ box d n := by
-- proof
  apply StatMech.Percolation.mem_boxFinset

/--
[mem_boxEdgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean)
-/
@[path]
private lemma mem_boxEdgeFinset_eq
  {d : ℕ}
  {d n : ℕ}
  {e : Sym2 (Site d)} :
-- imply
  e ∈ boxEdgeFinset d n ↔ ∃ x y, x ∈ box d n ∧ y ∈ box d n ∧ e = s(x, y) := by
-- proof
  apply StatMech.Percolation.mem_boxEdgeFinset

/--
[coord_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean)
-/
@[path]
private lemma coord_of_agree_eq
  {d : ℕ}
  {n : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : ∀ e ∈ (boxEdgeFinset d n : Set (Sym2 (Site d))), ω e = ω' e)
  (hx : x ∈ box d n)
  (hy : y ∈ box d n) :
-- imply
  ω s(x, y) = ω' s(x, y) := by
-- proof
  apply StatMech.Percolation.coord_of_agree n h x y hx hy

/--
[mem_boxCrossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean)
-/
@[path]
private lemma mem_boxCrossingEvent_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  ω ∈ boxCrossingEvent d n ↔ ∃ (x : Site d) (hx : x ∈ box d n), x ∈ vertexBoundary d n ∧ ∃ (h0 : origin d ∈ box d n), ConnectedWithin d ω (box d n) ⟨origin d, h0⟩ ⟨x, hx⟩ := by
-- proof
  apply StatMech.Percolation.mem_boxCrossingEvent

/--
[openSubgraphInduce_box_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean)
-/
@[path]
private lemma openSubgraphInduce_box_congr_eq
  {d : ℕ}
  {n : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (h : ∀ x y : Site d, x ∈ box d n → y ∈ box d n → ω s(x, y) = ω' s(x, y)) :
-- imply
  openSubgraphInduce d ω (box d n) = openSubgraphInduce d ω' (box d n) := by
-- proof
  apply StatMech.Percolation.openSubgraphInduce_box_congr n h

/--
[boxCrossingEvent_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean)
-/
@[path]
private lemma boxCrossingEvent_congr_eq
  {d : ℕ}
  {n : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (h : ∀ e ∈ (boxEdgeFinset d n : Set (Sym2 (Site d))), ω e = ω' e) :
-- imply
  ω ∈ boxCrossingEvent d n ↔ ω' ∈ boxCrossingEvent d n := by
-- proof
  apply StatMech.Percolation.boxCrossingEvent_congr n h

/--
[boxCrossingEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean)
-/
@[path]
private lemma boxCrossingEvent_dependsOn_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  DependsOn ((boxCrossingEvent d n).indicator (fun _ => (1 : ℝ))) ((boxEdgeFinset d n : Set (Sym2 (Site d)))) := by
-- proof
  apply StatMech.Percolation.boxCrossingEvent_dependsOn n

/--
[boxCrossingEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean)
-/
@[path]
private lemma boxCrossingEvent_isIncreasing_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  IsIncreasing (boxCrossingEvent d n) := by
-- proof
  apply StatMech.Percolation.boxCrossingEvent_isIncreasing n

/--
[boxCrossProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean)
-/
@[path]
private lemma boxCrossProb_nonneg_eq
  {d : ℕ}
  {d : ℕ}
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  0 ≤ boxCrossProb d p hp n := by
-- proof
  apply StatMech.Percolation.boxCrossProb_nonneg d p hp n

/--
[boxCrossProb_eq_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean)
-/
@[path]
private lemma boxCrossProb_eq_prob_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  boxCrossProb d p hp n = prob (p : ℝ) ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n)) := by
-- proof
  apply StatMech.Percolation.boxCrossProb_eq_prob p hp n

/--
[hasDerivAt_boxCrossProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean)
-/
@[path]
private lemma hasDerivAt_boxCrossProb_eq
  {d : ℕ}
  {n : ℕ}
  {q : ℝ} :
-- imply
  HasDerivAt (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) (∑ e : ↥(boxEdgeFinset d n), pivotalProb q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n)) e) q := by
-- proof
  apply StatMech.Percolation.hasDerivAt_boxCrossProb n q

/--
[deriv_boxCrossProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean)
-/
@[path]
private lemma deriv_boxCrossProb_eq
  {d : ℕ}
  {n : ℕ}
  {q : ℝ} :
-- imply
  deriv (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) q = ∑ e : ↥(boxEdgeFinset d n), pivotalProb q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n)) e := by
-- proof
  apply StatMech.Percolation.deriv_boxCrossProb n q

/--
[differentiable_boxCrossProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean)
-/
@[path]
private lemma differentiable_boxCrossProb_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  Differentiable ℝ (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) := by
-- proof
  apply StatMech.Percolation.differentiable_boxCrossProb n

/--
[deriv_boxCrossProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean)
-/
@[path]
private lemma deriv_boxCrossProb_nonneg_eq
  {d : ℕ}
  {n : ℕ}
  {q : ℝ}
-- given
  (hq0 : 0 ≤ q)
  (hq1 : q ≤ 1) :
-- imply
  0 ≤ deriv (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) q := by
-- proof
  apply StatMech.Percolation.deriv_boxCrossProb_nonneg n q hq0 hq1


-- created on 2026-10-23
