import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
open MeasureTheory Set Filter Finset SimpleGraph StatMech StatMech.Percolation


/--
[finset_subset_box_su](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean)
-/
@[path]
private lemma finset_subset_box_su_eq
  {d : ℕ}
  {S : Finset (Site d)} :
-- imply
  ∃ N : ℕ, (S : Set (Site d)) ⊆ box d N := by
-- proof
  apply StatMech.Percolation.finset_subset_box_su S

/--
[connWithinProb_le_one_su](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean)
-/
@[path]
private lemma connWithinProb_le_one_su_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {x : Site d}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  connWithinProb d p hp S x ≤ 1 := by
-- proof
  apply StatMech.Percolation.connWithinProb_le_one_su p hp S x

/--
[card_boundaryEdges_le_su](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean)
-/
@[path]
private lemma card_boundaryEdges_le_su_eq
  {d : ℕ}
  {S : Finset (Site d)} :
-- imply
  (boundaryEdges d S).card ≤ S.card * (2 * d) := by
-- proof
  apply StatMech.Percolation.card_boundaryEdges_le_su S

/--
[phi_le_card_su](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean)
-/
@[path]
private lemma phi_le_card_su_eq
  {d : ℕ}
  {S : Finset (Site d)}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  phi d p hp S ≤ (p : ℝ) * (boundaryEdges d S).card := by
-- proof
  apply StatMech.Percolation.phi_le_card_su p hp S

/--
[tildePc_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean)
-/
@[path]
private lemma tildePc_pos_eq
  {d : ℕ}
-- given
  (hd : 0 < d) :
-- imply
  0 < (tildePc d : ℝ) := by
-- proof
  apply StatMech.Percolation.tildePc_pos hd

/--
[wordEvent_adj_su](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean)
-/
@[path]
private lemma wordEvent_adj_su_eq
  {d : ℕ}
  {g : ℕ → Fin d × Bool}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {k : ℕ}
-- given
  (hω : ω ∈ wordEvent g n)
  (hk : k < n) :
-- imply
  (openSubgraph d ω).Adj (vertOf g k) (vertOf g (k + 1)) := by
-- proof
  apply StatMech.Percolation.wordEvent_adj_su g n hω k hk

/--
[wordEvent_connected_su](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean)
-/
@[path]
private lemma wordEvent_connected_su_eq
  {d : ℕ}
  {g : ℕ → Fin d × Bool}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hω : ω ∈ wordEvent g n) :
-- imply
  Connected d ω (origin d) (vertOf g n) := by
-- proof
  apply StatMech.Percolation.wordEvent_connected_su g n hω

/--
[lineWord_coord0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean)
-/
@[path]
private lemma lineWord_coord0_eq
  {d : ℕ}
  {k : ℕ}
-- given
  (hd : 0 < d) :
-- imply
  (vertOf (lineWord hd) k) ⟨0, hd⟩ = (k : ℤ) := by
-- proof
  apply StatMech.Percolation.lineWord_coord0 hd k

/--
[wordEvent_measure_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean)
-/
@[path]
private lemma wordEvent_measure_one_eq
  {d : ℕ}
  {g : ℕ → Fin d × Bool}
  {n : ℕ}
-- given
  (h0 : (1 : ℝ≥0) ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) 1 h0) (wordEvent g n) = 1 := by
-- proof
  apply StatMech.Percolation.wordEvent_measure_one g n h0

/--
[crossProb_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean)
-/
@[path]
private lemma crossProb_one_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 0 < d)
  (h0 : (1 : ℝ≥0) ≤ 1) :
-- imply
  crossProb d 1 h0 (n + 1) = 1 := by
-- proof
  apply StatMech.Percolation.crossProb_one hd h0 n

/--
[theta_one_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean)
-/
@[path]
private lemma theta_one_eq_one_eq
  {d : ℕ}
-- given
  (hd : 0 < d)
  (h0 : (1 : ℝ≥0) ≤ 1) :
-- imply
  theta d 1 h0 = 1 := by
-- proof
  apply StatMech.Percolation.theta_one_eq_one hd h0

/--
[theta_one_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean)
-/
@[path]
private lemma theta_one_ne_zero_eq
  {d : ℕ}
-- given
  (hd : 0 < d) :
-- imply
  ∀ h1 : (1 : ℝ≥0) ≤ 1, theta d 1 h1 ≠ 0 := by
-- proof
  apply StatMech.Percolation.theta_one_ne_zero hd

/--
[hsub_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean)
-/
@[path]
private lemma hsub_unconditional_eq
  {d : ℕ} :
-- imply
  ∀ p ∈ tildePcSet d, ∀ hp : p ≤ 1, ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n) := by
-- proof
  apply StatMech.Percolation.hsub_unconditional

/--
[sharpness_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean)
-/
@[path]
private lemma sharpness_unconditional_eq
  {d : ℕ}
-- given
  (hd : 0 < d) :
-- imply
  tildePc d = pc d ∧ (∀ p ∈ tildePcSet d, ∀ hp : p ≤ 1, ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n)) ∧ (∀ q : ℝ≥0, ∀ hq : q ≤ 1, tildePc d < q → (q : ℝ) < 1 → theta d q hq ≥ ((q : ℝ) - (tildePc d : ℝ)) / ((q : ℝ) * (1 - (tildePc d : ℝ)))) := by
-- proof
  apply StatMech.Percolation.sharpness_unconditional hd


-- created on 2026-10-23
