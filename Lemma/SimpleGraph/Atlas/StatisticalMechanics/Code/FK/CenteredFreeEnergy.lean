import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.CenteredFreeEnergy.Part3
open SimpleGraph Filter Topology Set MeasureTheory StatMech StatMech.FK


/--
[cfe_centered_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_centered_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℝ} :
-- imply
  cfe_centered G q 0 = 0 := by
-- proof
  apply StatMech.FK.cfe_centered_zero G q

/--
[cfe_centered_convexOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_centered_convexOn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℝ}
-- given
  (hq : 0 < q)
  (hE : 0 < G.edgeFinset.card) :
-- imply
  ConvexOn ℝ univ (cfe_centered G q) := by
-- proof
  apply StatMech.FK.cfe_centered_convexOn G q hq hE

/--
[cfe_centered_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_centered_hasDerivAt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {t : ℝ}
-- given
  (hE : 0 < G.edgeFinset.card) :
-- imply
  HasDerivAt (cfe_centered G 2) (fpd_avgDensity G t) t := by
-- proof
  apply StatMech.FK.cfe_centered_hasDerivAt G hE t

/--
[cfe_avgDensity_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_avgDensity_mem_Icc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {t : ℝ}
-- given
  (hE : 0 < G.edgeFinset.card) :
-- imply
  0 ≤ fpd_avgDensity G t ∧ fpd_avgDensity G t ≤ 1 := by
-- proof
  apply StatMech.FK.cfe_avgDensity_mem_Icc G hE t

/--
[cfe_centered_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_centered_monotone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hE : 0 < G.edgeFinset.card) :
-- imply
  Monotone (cfe_centered G 2) := by
-- proof
  apply StatMech.FK.cfe_centered_monotone G hE

/--
[cfe_id_sub_centered_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_id_sub_centered_monotone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hE : 0 < G.edgeFinset.card) :
-- imply
  Monotone (fun t => t - cfe_centered G 2 t) := by
-- proof
  apply StatMech.FK.cfe_id_sub_centered_monotone G hE

/--
[cfe_centered_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_centered_abs_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {t : ℝ}
-- given
  (hE : 0 < G.edgeFinset.card) :
-- imply
  |cfe_centered G 2 t| ≤ |t| := by
-- proof
  apply StatMech.FK.cfe_centered_abs_le G hE t

/--
[cfe_wiredCentered_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_wiredCentered_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  cfe_wiredCentered G bdry q 0 = 0 := by
-- proof
  apply StatMech.FK.cfe_wiredCentered_zero G bdry q

/--
[cfe_wiredCentered_convexOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_wiredCentered_convexOn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℝ}
-- given
  (bdry : V → Prop)
  (hq : 0 < q)
  (hE : 0 < G.edgeFinset.card) :
-- imply
  ConvexOn ℝ univ (cfe_wiredCentered G bdry q) := by
-- proof
  apply StatMech.FK.cfe_wiredCentered_convexOn G bdry q hq hE

/--
[cfe_wiredCentered_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_wiredCentered_hasDerivAt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {t : ℝ}
-- given
  (bdry : V → Prop)
  (hE : 0 < G.edgeFinset.card) :
-- imply
  HasDerivAt (cfe_wiredCentered G bdry 2) (wpd_avgWiredDensity G bdry 2 t) t := by
-- proof
  apply StatMech.FK.cfe_wiredCentered_hasDerivAt G bdry hE t

/--
[cfe_centered_limit_convexOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_centered_limit_convexOn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {G : ℝ → ℝ}
-- given
  (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hconv : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t))) :
-- imply
  ConvexOn ℝ univ G := by
-- proof
  apply StatMech.FK.cfe_centered_limit_convexOn G hE hconv

/--
[cfe_wiredCentered_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_wiredCentered_tendsto_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {G : ℝ → ℝ}
  {t : ℝ}
-- given
  (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hfree : Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
  (hsv : Tendsto (fun n => ((Finset.univ.filter (boxBoundary d n)).card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 (G t)) := by
-- proof
  apply StatMech.FK.cfe_wiredCentered_tendsto G hE t hfree hsv

/--
[cfe_genuineFreeIsLeftDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_genuineFreeIsLeftDeriv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {N : ℕ}
  {G : ℝ → ℝ}
-- given
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hG : ConvexOn ℝ univ G)
  (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
  (hcol : fpe2_GenuineFreeCollapse d N) :
-- imply
  fpe2_GenuineFreeIsLeftDeriv d N G := by
-- proof
  apply StatMech.FK.cfe_genuineFreeIsLeftDeriv G N hEbox hG hboxfree hcol

/--
[cfe_genuineWiredIsRightDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_genuineWiredIsRightDeriv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {N : ℕ}
  {G : ℝ → ℝ}
-- given
  (hd : 1 ≤ d)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hG : ConvexOn ℝ univ G)
  (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
  (hcolfree : fpe2_GenuineFreeCollapse d N)
  (hcolwired : fpe2_GenuineWiredCollapse d N) :
-- imply
  fpe2_GenuineWiredIsRightDeriv d N G := by
-- proof
  apply StatMech.FK.cfe_genuineWiredIsRightDeriv G hd N hEbox hG hboxfree hcolfree hcolwired

/--
[cfe_fk_uniqueness_of_centeredConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_fk_uniqueness_of_centeredConvergence_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {G : ℝ → ℝ}
-- given
  (hd : 1 ≤ d)
  (heb : eb ∈ (boxGraph d N).edgeFinset)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hG : ConvexOn ℝ univ G)
  (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
  (hcolfree : fpe2_GenuineFreeCollapse d N)
  (hcolwired : fpe2_GenuineWiredCollapse d N) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.cfe_fk_uniqueness_of_centeredConvergence G hd N eb heb hEbox hG hboxfree hcolfree hcolwired

/--
[cfe_fk_uniqueness_of_centeredData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_fk_uniqueness_of_centeredData_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {G : ℝ → ℝ}
-- given
  (hd : 1 ≤ d)
  (heb : eb ∈ (boxGraph d N).edgeFinset)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hG : ConvexOn ℝ univ G)
  (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t))) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.cfe_fk_uniqueness_of_centeredData G hd N eb heb hEbox hG hboxfree

/--
[cfe_centeredConvergence_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_centeredConvergence_satisfiable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ} :
-- imply
  ∃ (gn : ℕ → ℝ → ℝ) (G : ℝ → ℝ), (∀ t, Tendsto (fun n => gn n t) atTop (𝓝 (G t))) ∧ G 0 = 0 ∧ ConvexOn ℝ univ G := by
-- proof
  apply StatMech.FK.cfe_centeredConvergence_satisfiable G

/--
[cfe_residue_remark](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean)
-/
@[path]
private lemma cfe_residue_remark_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ} :
-- imply
  True := by
-- proof
  apply StatMech.FK.cfe_residue_remark G


-- created on 2026-10-23
