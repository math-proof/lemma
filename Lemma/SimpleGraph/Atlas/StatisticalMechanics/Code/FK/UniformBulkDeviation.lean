import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.UniformBulkDeviation.Part2
open MeasureTheory Set Filter Topology Real StatMech StatMech.FK


/--
[ubd_freeDensity_le_rightDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_freeDensity_le_rightDeriv_eq
  {d : ℕ}
  {N : ℕ}
  {g : ℝ → ℝ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
  (hcol : ubd_FreeGrowingBoxCollapse (d := d) N) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ≤ pressureRightDeriv g t := by
-- proof
  apply StatMech.FK.ubd_freeDensity_le_rightDeriv N hEbox g hg hboxfree hcol e' t

/--
[ubd_leftDeriv_le_freeDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_leftDeriv_le_freeDensity_eq
  {d : ℕ}
  {N : ℕ}
  {g : ℝ → ℝ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
  (hcol : ubd_FreeGrowingBoxCollapse (d := d) N) :
-- imply
  pressureLeftDeriv g t ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) := by
-- proof
  apply StatMech.FK.ubd_leftDeriv_le_freeDensity N hEbox g hg hboxfree hcol e' t

/--
[ubd_freeDensityIsLeftDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_freeDensityIsLeftDeriv_eq
  {d : ℕ}
  {N : ℕ}
  {g : ℝ → ℝ}
-- given
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
  (hcol : ubd_FreeGrowingBoxCollapse (d := d) N) :
-- imply
  fdd_FreeDensityIsLeftDeriv (d := d) N g := by
-- proof
  apply StatMech.FK.ubd_freeDensityIsLeftDeriv N hEbox g hg hboxfree hcol

/--
[ubd_leftDeriv_le_wiredDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_leftDeriv_le_wiredDensity_eq
  {d : ℕ}
  {N : ℕ}
  {g : ℝ → ℝ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
  (hcol : ubd_FreeGrowingBoxCollapse (d := d) N) :
-- imply
  pressureLeftDeriv g t ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) := by
-- proof
  apply StatMech.FK.ubd_leftDeriv_le_wiredDensity N hEbox g hg hboxfree hcol e' t

/--
[ubd_wiredDensityIsRightDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_wiredDensityIsRightDeriv_eq
  {d : ℕ}
  {N : ℕ}
  {g : ℝ → ℝ}
-- given
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
  (hcol : ubd_FreeGrowingBoxCollapse (d := d) N)
  (hub : fdd_WiredDensityUpperBound (d := d) N g) :
-- imply
  fdd_WiredDensityIsRightDeriv (d := d) N g := by
-- proof
  apply StatMech.FK.ubd_wiredDensityIsRightDeriv N hEbox g hg hboxfree hcol hub

/--
[ubd_fk_uniqueness_of_growingBoxCollapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_fk_uniqueness_of_growingBoxCollapse_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {g : ℝ → ℝ}
-- given
  (hd : 1 ≤ d)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
  (hcolfree : ubd_FreeGrowingBoxCollapse (d := d) N)
  (hcolwired : wpd_AvgWiredDensityCollapse (d := d) N) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.ubd_fk_uniqueness_of_growingBoxCollapse hd N eb hEbox hg hboxfree hcolfree hcolwired

/--
[ubd_freeEdgeDensity_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_freeEdgeDensity_mem_Icc_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ} :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ∈ Set.Icc (0:ℝ) 1 := by
-- proof
  apply StatMech.FK.ubd_freeEdgeDensity_mem_Icc N e' t

/--
[ubd_edgeMargProb_wiredFkProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_edgeMargProb_wiredFkProb_nonneg_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
  {e : Sym2 V}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 ≤ edgeMargProb (wiredFkProb G bdry p q) e := by
-- proof
  apply StatMech.FK.ubd_edgeMargProb_wiredFkProb_nonneg G bdry hp hp1 hq e

/--
[ubd_edgeMargProb_wiredFkProb_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_edgeMargProb_wiredFkProb_le_one_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
  {e : Sym2 V}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  edgeMargProb (wiredFkProb G bdry p q) e ≤ 1 := by
-- proof
  apply StatMech.FK.ubd_edgeMargProb_wiredFkProb_le_one G bdry hp hp1 hq e

/--
[ubd_wiredEdgeDensity_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_wiredEdgeDensity_mem_Icc_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ} :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ∈ Set.Icc (0:ℝ) 1 := by
-- proof
  apply StatMech.FK.ubd_wiredEdgeDensity_mem_Icc N e' t

/--
[ubd_avgWiredDensity_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_avgWiredDensity_eq_sum_eq
  {d : ℕ}
  {n : ℕ}
  {t : ℝ} :
-- imply
  wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t = (1 / ((boxGraph d n).edgeFinset.card : ℝ)) * ∑ e ∈ (boxGraph d n).edgeFinset, edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e := by
-- proof
  apply StatMech.FK.ubd_avgWiredDensity_eq_sum n t

/--
[ubd_growingBox_wiredCollapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_growingBox_wiredCollapse_eq
  {d : ℕ}
  {t : ℝ}
  {L : ℝ}
  {In : (n : ℕ) → Finset (Sym2 (boxVerts d n))}
  {δ : ℕ → ℝ}
-- given
  (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hL0 : 0 ≤ L)
  (hL1 : L ≤ 1)
  (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
  (hδ0 : ∀ n, 0 ≤ δ n)
  (hδlim : Tendsto δ atTop (𝓝 0))
  (hin : ∀ n, ∀ e ∈ In n, |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e - L| ≤ δ n)
  (hbdy : Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.ubd_growingBox_wiredCollapse t hE L hL0 hL1 In hIE δ hδ0 hδlim hin hbdy

/--
[ubd_freeGrowingBoxCollapse_of_uniformBulk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_freeGrowingBoxCollapse_of_uniformBulk_eq
  {d : ℕ}
  {N : ℕ}
-- given
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hubd : ubd_FreeUniformBulkDeviation (d := d) N) :
-- imply
  ubd_FreeGrowingBoxCollapse (d := d) N := by
-- proof
  apply StatMech.FK.ubd_freeGrowingBoxCollapse_of_uniformBulk N hEbox hubd

/--
[ubd_wiredGrowingBoxCollapse_of_uniformBulk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_wiredGrowingBoxCollapse_of_uniformBulk_eq
  {d : ℕ}
  {N : ℕ}
-- given
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hubd : ubd_WiredUniformBulkDeviation (d := d) N) :
-- imply
  wpd_AvgWiredDensityCollapse (d := d) N := by
-- proof
  apply StatMech.FK.ubd_wiredGrowingBoxCollapse_of_uniformBulk N hEbox hubd

/--
[ubd_fk_uniqueness_of_uniformBulk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_fk_uniqueness_of_uniformBulk_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {g : ℝ → ℝ}
-- given
  (hd : 1 ≤ d)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
  (hfreeBulk : ubd_FreeUniformBulkDeviation (d := d) N)
  (hwiredBulk : ubd_WiredUniformBulkDeviation (d := d) N) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.ubd_fk_uniqueness_of_uniformBulk hd N eb hEbox hg hboxfree hfreeBulk hwiredBulk

/--
[ubd_wiredEdgeDensity_translation_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_wiredEdgeDensity_translation_invariant_eq
  {d : ℕ}
  {p : ℝ}
  {g : Multiplicative (Site d)}
  {e : Sym2 (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent {e}) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (({e} : Finset (Sym2 (Site d))).image (fun e => g⁻¹ • e))) := by
-- proof
  apply StatMech.FK.ubd_wiredEdgeDensity_translation_invariant hp hp1 g e

/--
[ubd_residue_remark](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean)
-/
@[path]
private lemma ubd_residue_remark_eq
  {d : ℕ} :
-- imply
  True := by
-- proof
  apply StatMech.FK.ubd_residue_remark


-- created on 2026-10-23
