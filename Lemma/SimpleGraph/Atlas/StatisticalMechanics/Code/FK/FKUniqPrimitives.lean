import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.FKUniqPrimitives
open MeasureTheory Set Filter Topology Real SimpleGraph Finset StatMech StatMech.FK


/--
[fup_boundary_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPrimitives.lean)
-/
@[path]
private lemma fup_boundary_card_eq_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  (Finset.univ.filter (boxBoundary d n)).card = boxSV_boundaryCard d n := by
-- proof
  apply StatMech.FK.fup_boundary_card_eq d n

/--
[fup_dart_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPrimitives.lean)
-/
@[path]
private lemma fup_dart_card_eq_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  Fintype.card (boxGraph d n).Dart = boxSV_edgeCard d n := by
-- proof
  apply StatMech.FK.fup_dart_card_eq d n

/--
[fup_edge_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPrimitives.lean)
-/
@[path]
private lemma fup_edge_card_eq_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  boxSV_edgeCard d n = 2 * (boxGraph d n).edgeFinset.card := by
-- proof
  apply StatMech.FK.fup_edge_card_eq d n

/--
[fup_surfaceVolume_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPrimitives.lean)
-/
@[path]
private lemma fup_surfaceVolume_tendsto_zero_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (fun n => ((Finset.univ.filter (boxBoundary d n)).card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.fup_surfaceVolume_tendsto_zero d hd

/--
[fup_fk_uniqueness_of_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPrimitives.lean)
-/
@[path]
private lemma fup_fk_uniqueness_of_collapse_eq
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
  (hwcol : wpd_AvgWiredDensityCollapse (d := d) N)
  (hflc : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ContinuousWithinAt (fun s => freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Iio t) t)
  (hwrc : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ContinuousWithinAt (fun s => wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Ioi t) t) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.fup_fk_uniqueness_of_collapse hd N eb Gn hEfree hEbox hg hfree hboxfree hcol hwcol hflc hwrc


-- created on 2026-10-23
