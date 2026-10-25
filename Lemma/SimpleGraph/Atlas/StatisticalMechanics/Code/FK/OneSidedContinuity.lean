import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.OneSidedContinuity
open MeasureTheory Set Filter Topology Real SimpleGraph Finset Function StatMech StatMech.FK


/--
[osc_fsc_logistic_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OneSidedContinuity.lean)
-/
@[path]
private lemma osc_fsc_logistic_continuous_eq
  {d : ℕ} :
-- imply
  Continuous fsc_logistic := by
-- proof
  apply StatMech.FK.osc_fsc_logistic_continuous

/--
[osc_edgeProduct_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OneSidedContinuity.lean)
-/
@[path]
private lemma osc_edgeProduct_continuous_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  Continuous (fun p : ℝ => edgeProduct G p ω) := by
-- proof
  apply StatMech.FK.osc_edgeProduct_continuous G ω

/--
[osc_freeBoxMarg_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OneSidedContinuity.lean)
-/
@[path]
private lemma osc_freeBoxMarg_continuous_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 V} :
-- imply
  Continuous (fun s : ℝ => edgeMargProb (fkProb G (fsc_logistic s) 2) e) := by
-- proof
  apply StatMech.FK.osc_freeBoxMarg_continuous G e

/--
[osc_wiredBoxMarg_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OneSidedContinuity.lean)
-/
@[path]
private lemma osc_wiredBoxMarg_continuous_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {e : Sym2 V}
-- given
  (bdry : V → Prop) :
-- imply
  Continuous (fun s : ℝ => edgeMargProb (wiredFkProb G bdry (fsc_logistic s) 2) e) := by
-- proof
  apply StatMech.FK.osc_wiredBoxMarg_continuous G bdry e

/--
[osc_fkEdgeMarg_monotone_in_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OneSidedContinuity.lean)
-/
@[path]
private lemma osc_fkEdgeMarg_monotone_in_p_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 V}
  {p1 p2 : ℝ}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hle : p1 ≤ p2) :
-- imply
  edgeMargProb (fkProb G p1 2) e ≤ edgeMargProb (fkProb G p2 2) e := by
-- proof
  apply StatMech.FK.osc_fkEdgeMarg_monotone_in_p G e hp1 hp1' hp2 hp2' hle

/--
[osc_freeEdgeDensity_q2_monotoneOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OneSidedContinuity.lean)
-/
@[path]
private lemma osc_freeEdgeDensity_q2_monotoneOn_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)} :
-- imply
  MonotoneOn (freeEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0 : ℝ) 1) := by
-- proof
  apply StatMech.FK.osc_freeEdgeDensity_q2_monotoneOn d N eb

/--
[osc_freeEdgeDensity_logistic_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OneSidedContinuity.lean)
-/
@[path]
private lemma osc_freeEdgeDensity_logistic_monotone_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)} :
-- imply
  Monotone (fun s => freeEdgeDensity d 2 (edgeIncl d N eb) (fsc_logistic s)) := by
-- proof
  apply StatMech.FK.osc_freeEdgeDensity_logistic_monotone d N eb

/--
[osc_wiredEdgeDensity_logistic_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OneSidedContinuity.lean)
-/
@[path]
private lemma osc_wiredEdgeDensity_logistic_monotone_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)} :
-- imply
  Monotone (fun s => wiredEdgeDensity d 2 (edgeIncl d N eb) (fsc_logistic s)) := by
-- proof
  apply StatMech.FK.osc_wiredEdgeDensity_logistic_monotone d N eb

/--
[osc_freeEdgeDensity_left_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OneSidedContinuity.lean)
-/
@[path]
private lemma osc_freeEdgeDensity_left_continuous_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {t : ℝ} :
-- imply
  ContinuousWithinAt (fun s => freeEdgeDensity d 2 (edgeIncl d N eb) (fsc_logistic s)) (Iio t) t := by
-- proof
  apply StatMech.FK.osc_freeEdgeDensity_left_continuous d N eb t

/--
[osc_wiredEdgeDensity_right_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OneSidedContinuity.lean)
-/
@[path]
private lemma osc_wiredEdgeDensity_right_continuous_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {t : ℝ} :
-- imply
  ContinuousWithinAt (fun s => wiredEdgeDensity d 2 (edgeIncl d N eb) (fsc_logistic s)) (Ioi t) t := by
-- proof
  apply StatMech.FK.osc_wiredEdgeDensity_right_continuous d N eb t

/--
[osc_fk_uniqueness_of_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OneSidedContinuity.lean)
-/
@[path]
private lemma osc_fk_uniqueness_of_collapse_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {Gn : ℕ → SimpleGraph (boxVerts d N)}
  [∀ n, DecidableRel (Gn n).Adj]
  {g : ℝ → ℝ}
-- given
  (hd : 1 ≤ d)
  (hEfree : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
  (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
  (hcol : fpd_AvgDensityCollapse d N Gn)
  (hwcol : wpd_AvgWiredDensityCollapse (d := d) N) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.osc_fk_uniqueness_of_collapse hd N eb Gn hEfree hEbox hg hfree hboxfree hcol hwcol


-- created on 2026-10-23
