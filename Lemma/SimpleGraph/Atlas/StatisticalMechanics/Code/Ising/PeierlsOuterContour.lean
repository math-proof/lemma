import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.PeierlsOuterContour.Part3
open MeasureTheory Filter Topology Finset SimpleGraph StatMech StatMech.Ising


/--
[poc_cyclesAtLen_card_le_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean)
-/
@[path]
private lemma poc_cyclesAtLen_card_le_real_eq
  {d : ℕ}
  {ℓ : ℕ} :
-- imply
  ((Percolation.cyclesAtLen ℓ).card : ℝ) ≤ 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ) := by
-- proof
  apply StatMech.Ising.poc_cyclesAtLen_card_le_real ℓ

/--
[poc_twoPeierlsBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean)
-/
@[path]
private lemma poc_twoPeierlsBound_nonneg_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ} :
-- imply
  0 ≤ twoPeierlsBound d β := by
-- proof
  apply StatMech.Ising.poc_twoPeierlsBound_nonneg d β

/--
[poc_twoPeierlsBound_tendsto_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean)
-/
@[path]
private lemma poc_twoPeierlsBound_tendsto_atTop_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  Tendsto (fun β : ℝ => twoPeierlsBound d β) atTop (nhds 0) := by
-- proof
  apply StatMech.Ising.poc_twoPeierlsBound_tendsto_atTop d

/--
[poc_exists_beta_two_peierlsBound_lt_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean)
-/
@[path]
private lemma poc_exists_beta_two_peierlsBound_lt_half_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β → twoPeierlsBound d β < 1 / 2 := by
-- proof
  apply StatMech.Ising.poc_exists_beta_two_peierlsBound_lt_half d

/--
[poc_circuitLengthSum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean)
-/
@[path]
private lemma poc_circuitLengthSum_le_eq
  {d : ℕ}
  {β : ℝ}
  {T : Finset ℕ}
-- given
  (hx : peierlsRatio 2 β < 1) :
-- imply
  ∑ ℓ ∈ T, ((Percolation.cyclesAtLen ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ)) ≤ twoPeierlsBound 2 β := by
-- proof
  apply StatMech.Ising.poc_circuitLengthSum_le β hx T

/--
[poc_probContourCircuit_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean)
-/
@[path]
private lemma poc_probContourCircuit_le_eq
  {d : ℕ}
  {n : ℕ}
  {K : Set (Site d)}
  {η : ConfigSpace (Site d)}
  {β : ℝ}
-- given
  (hK : K ⊆ box d n) :
-- imply
  probContour K η n (bondFinsetTouch d n) β ≤ Real.exp (-(2 * β) * (contourLen K (bondFinsetTouch d n) : ℝ)) := by
-- proof
  apply StatMech.Ising.poc_probContourCircuit_le n K hK η β

/--
[poc_circuitSummand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean)
-/
@[path]
private lemma poc_circuitSummand_nonneg_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ}
  {interiorOf : InteriorAssignment}
  {σ : Σ _ℓ : ℕ, Σ u : Site 2, (hypercubicLattice 2).Walk u u} :
-- imply
  0 ≤ poc_circuitSummand n β interiorOf σ := by
-- proof
  apply StatMech.Ising.poc_circuitSummand_nonneg n β interiorOf σ

/--
[poc_mem_circuitFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean)
-/
@[path]
private lemma poc_mem_circuitFamily_eq
  {d : ℕ}
  {M ℓ : ℕ}
  {u : Site 2}
  {γ : (hypercubicLattice 2).Walk u u}
-- given
  (hℓM : ℓ < M)
  (hu : u ∈ anchorFinset ℓ)
  (hlen : γ.length = ℓ)
  (hcyc : γ.IsCycle) :
-- imply
  (⟨ℓ, ⟨u, γ⟩⟩ : Σ _ℓ : ℕ, Σ u : Site 2, (hypercubicLattice 2).Walk u u) ∈ poc_circuitFamily M := by
-- proof
  apply StatMech.Ising.poc_mem_circuitFamily hℓM hu hlen hcyc

/--
[poc_probOriginMinus_le_circuitSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean)
-/
@[path]
private lemma poc_probOriginMinus_le_circuitSum_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ}
-- given
  (hMap : OuterContourMap n) :
-- imply
  probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0 ≤ ∑ σ ∈ poc_circuitFamily (2 * 2 * (boxFinset 2 n).card + 1), poc_circuitSummand n β (Classical.choose hMap) σ := by
-- proof
  apply StatMech.Ising.poc_probOriginMinus_le_circuitSum n β hMap

/--
[poc_circuitSum_le_lengthSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean)
-/
@[path]
private lemma poc_circuitSum_le_lengthSum_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ}
  {M : ℕ}
  {interiorOf : InteriorAssignment}
-- given
  (hglob : ∀ (ℓ : ℕ) (u : Site 2) (γ : (hypercubicLattice 2).Walk u u), u ∈ anchorFinset ℓ → γ.length = ℓ → γ.IsCycle → (↑(interiorOf u γ) : Set (Site 2)) ⊆ box 2 n ∧ contourLen (↑(interiorOf u γ)) (bondFinsetTouch 2 n) = ℓ) :
-- imply
  ∑ σ ∈ poc_circuitFamily M, poc_circuitSummand n β interiorOf σ ≤ ∑ ℓ ∈ Finset.range M, ((Percolation.cyclesAtLen ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ)) := by
-- proof
  apply StatMech.Ising.poc_circuitSum_le_lengthSum n β M interiorOf hglob

/--
[poc_probOriginMinus_le_two_peierls](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean)
-/
@[path]
private lemma poc_probOriginMinus_le_two_peierls_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ}
-- given
  (hx : peierlsRatio 2 β < 1)
  (hMap : OuterContourMap n) :
-- imply
  probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0 ≤ twoPeierlsBound 2 β := by
-- proof
  apply StatMech.Ising.poc_probOriginMinus_le_two_peierls n β hx hMap

/--
[poc_peierls_long_range_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean)
-/
@[path]
private lemma poc_peierls_long_range_order_eq
  {d : ℕ}
-- given
  (hMap : ∀ n : ℕ, OuterContourMap n) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 := by
-- proof
  apply StatMech.Ising.poc_peierls_long_range_order hMap


-- created on 2026-10-23
