import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.GenuineEdgeCollapse
open MeasureTheory Filter Topology SimpleGraph Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[gec_freeSandwich_of_rotation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/GenuineEdgeCollapse.lean)
-/
@[path]
private lemma gec_freeSandwich_of_rotation_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hd : 1 ≤ d)
  (hres : ocs_FreeRotationResidue (d := d) N e' t) :
-- imply
  ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ), (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧ (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧ (∀ n, ∀ e ∈ In n, freeEdgeDensity d 2 (edgeIncl d n e) (fsc_logistic t) = freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)) ∧ (∀ n, ∀ e ∈ In n, freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - δ n ≤ edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e) ∧ Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.gec_freeSandwich_of_rotation hd N e' t hres

/--
[gec_wiredSandwich_of_rotation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/GenuineEdgeCollapse.lean)
-/
@[path]
private lemma gec_wiredSandwich_of_rotation_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hd : 1 ≤ d)
  (hres : ocs_WiredRotationResidue (d := d) N e' t) :
-- imply
  ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ), (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧ (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧ (∀ n, ∀ e ∈ In n, wiredEdgeDensity d 2 (edgeIncl d n e) (fsc_logistic t) = wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)) ∧ (∀ n, ∀ e ∈ In n, edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) + δ n) ∧ Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.gec_wiredSandwich_of_rotation hd N e' t hres

/--
[gec_freeBulk_of_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/GenuineEdgeCollapse.lean)
-/
@[path]
private lemma gec_freeBulk_of_sandwich_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hsand : ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ), (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧ (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧ (∀ n, ∀ e ∈ In n, freeEdgeDensity d 2 (edgeIncl d n e) (fsc_logistic t) = freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)) ∧ (∀ n, ∀ e ∈ In n, freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - δ n ≤ edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e) ∧ Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (𝓝 0)) :
-- imply
  ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ), (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧ (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧ (∀ n, ∀ e ∈ In n, |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e - freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)| ≤ δ n) ∧ Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.gec_freeBulk_of_sandwich N e' t hsand

/--
[gec_wiredBulk_of_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/GenuineEdgeCollapse.lean)
-/
@[path]
private lemma gec_wiredBulk_of_sandwich_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hsand : ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ), (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧ (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧ (∀ n, ∀ e ∈ In n, wiredEdgeDensity d 2 (edgeIncl d n e) (fsc_logistic t) = wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)) ∧ (∀ n, ∀ e ∈ In n, edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) + δ n) ∧ Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (𝓝 0)) :
-- imply
  ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ), (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧ (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧ (∀ n, ∀ e ∈ In n, |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e - wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)| ≤ δ n) ∧ Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.gec_wiredBulk_of_sandwich N e' t hsand

/--
[gec_freeCollapse_of_bulk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/GenuineEdgeCollapse.lean)
-/
@[path]
private lemma gec_freeCollapse_of_bulk_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hbulk : ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ), (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧ (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧ (∀ n, ∀ e ∈ In n, |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e - freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)| ≤ δ n) ∧ Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => fpd_avgDensity (boxGraph d n) t) atTop (𝓝 (freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t))) := by
-- proof
  apply StatMech.FK.gec_freeCollapse_of_bulk N e' t hEbox hbulk

/--
[gec_wiredCollapse_of_bulk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/GenuineEdgeCollapse.lean)
-/
@[path]
private lemma gec_wiredCollapse_of_bulk_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hbulk : ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ), (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧ (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧ (∀ n, ∀ e ∈ In n, |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e - wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)| ≤ δ n) ∧ Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t))) := by
-- proof
  apply StatMech.FK.gec_wiredCollapse_of_bulk N e' t hEbox hbulk

/--
[gec_GenuineFreeCollapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/GenuineEdgeCollapse.lean)
-/
@[path]
private lemma gec_GenuineFreeCollapse_eq
  {d : ℕ}
  {N : ℕ}
-- given
  (hd : 1 ≤ d)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card) :
-- imply
  fpe2_GenuineFreeCollapse (d := d) N := by
-- proof
  apply StatMech.FK.gec_GenuineFreeCollapse hd N hEbox

/--
[gec_GenuineWiredCollapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/GenuineEdgeCollapse.lean)
-/
@[path]
private lemma gec_GenuineWiredCollapse_eq
  {d : ℕ}
  {N : ℕ}
-- given
  (hd : 1 ≤ d)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card) :
-- imply
  fpe2_GenuineWiredCollapse (d := d) N := by
-- proof
  apply StatMech.FK.gec_GenuineWiredCollapse hd N hEbox

/--
[gec_fk_uniqueness_of_perVolume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/GenuineEdgeCollapse.lean)
-/
@[path]
private lemma gec_fk_uniqueness_of_perVolume_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hd : 1 ≤ d)
  (heb : eb ∈ (boxGraph d N).edgeFinset)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hdata : ∀ t, bpv_PerVolumeFreeEnergyData d t) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.gec_fk_uniqueness_of_perVolume hd N eb heb hEbox hdata


-- created on 2026-10-23
