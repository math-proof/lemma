import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardShiftedCycleAssembly.Part6
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[kwGraphFormalRoot_coeff_surfaceQuadratic_shifted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean)
-/
@[path]
private lemma kwGraphFormalRoot_coeff_surfaceQuadratic_shifted_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {lambda : SurfaceSpinStructure g}
  {S : Finset (Sym2 V)}
-- given
  (phase : G.Dart -> G.Dart -> Complex)
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (hlog : KWGraphWeightedCycleLog G phase (surfaceSpinCycleCoefficient edgeClass lambda))
  (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
  (hdeg : forall vertex, G.degree vertex <= 3)
  (hS : S ∈ evenSubgraphs G) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) (kwGraphFormalRoot G phase) = (surfaceParitySign (surfaceQuadraticParity lambda (surfaceSubgraphHomology edgeClass S)) : Complex) := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_coeff_surfaceQuadratic_shifted G phase edgeClass lambda hlog hisotropic hdeg S hS

/--
[surfaceSpinFormalEvenPolynomial_eq_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean)
-/
@[path]
private lemma surfaceSpinFormalEvenPolynomial_eq_coe_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {lambda : SurfaceSpinStructure g}
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g) :
-- imply
  surfaceSpinFormalEvenPolynomial G edgeClass lambda = (surfaceSpinEvenMvPolynomial G edgeClass lambda : MvPowerSeries (Sym2 V) Complex) := by
-- proof
  apply StatMech.FrontierA.surfaceSpinFormalEvenPolynomial_eq_coe G edgeClass lambda

/--
[surfaceSpinFormalEvenPolynomial_coeff_finsetExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean)
-/
@[path]
private lemma surfaceSpinFormalEvenPolynomial_coeff_finsetExponent_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {lambda : SurfaceSpinStructure g}
  {S : Finset (Sym2 V)}
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) (surfaceSpinFormalEvenPolynomial G edgeClass lambda) = if S ∈ evenSubgraphs G then surfaceSpinCycleCoefficient edgeClass lambda S else 0 := by
-- proof
  apply StatMech.FrontierA.surfaceSpinFormalEvenPolynomial_coeff_finsetExponent G edgeClass lambda S

/--
[surfaceSpinFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean)
-/
@[path]
private lemma surfaceSpinFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {lambda : SurfaceSpinStructure g}
  {m : Sym2 V →₀ Nat}
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (hm : ¬ ons_IsSquarefreeExponent m) :
-- imply
  MvPowerSeries.coeff m (surfaceSpinFormalEvenPolynomial G edgeClass lambda) = 0 := by
-- proof
  apply StatMech.FrontierA.surfaceSpinFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree G edgeClass lambda m hm

/--
[kwGraphFormalRoot_eq_surfaceSpinFormalEvenPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean)
-/
@[path]
private lemma kwGraphFormalRoot_eq_surfaceSpinFormalEvenPolynomial_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {lambda : SurfaceSpinStructure g}
-- given
  (phase : G.Dart -> G.Dart -> Complex)
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (hlog : KWGraphWeightedCycleLog G phase (surfaceSpinCycleCoefficient edgeClass lambda))
  (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
  (hdeg : ∀ vertex, G.degree vertex <= 3)
  (hnonsquare : ∀ m : Sym2 V →₀ Nat, ¬ ons_IsSquarefreeExponent m -> MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0) :
-- imply
  kwGraphFormalRoot G phase = surfaceSpinFormalEvenPolynomial G edgeClass lambda := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_eq_surfaceSpinFormalEvenPolynomial G phase edgeClass lambda hlog hisotropic hdeg hnonsquare

/--
[surfaceSpinEvenMvPolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean)
-/
@[path]
private lemma surfaceSpinEvenMvPolynomial_eval_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {lambda : SurfaceSpinStructure g}
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (weight : Sym2 V -> Complex) :
-- imply
  MvPolynomial.eval weight (surfaceSpinEvenMvPolynomial G edgeClass lambda) = surfaceQuadraticEvenPolynomial G edgeClass lambda weight := by
-- proof
  apply StatMech.FrontierA.surfaceSpinEvenMvPolynomial_eval G edgeClass lambda weight

/--
[surfaceSpinFormalEvenPolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean)
-/
@[path]
private lemma surfaceSpinFormalEvenPolynomial_eval_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {lambda : SurfaceSpinStructure g}
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (weight : Sym2 V -> Complex) :
-- imply
  ons_mvSeriesEval (surfaceSpinFormalEvenPolynomial G edgeClass lambda) weight = surfaceQuadraticEvenPolynomial G edgeClass lambda weight := by
-- proof
  apply StatMech.FrontierA.surfaceSpinFormalEvenPolynomial_eval G edgeClass lambda weight

/--
[surfaceSpinScalePolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean)
-/
@[path]
private lemma surfaceSpinScalePolynomial_eval_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {lambda : SurfaceSpinStructure g}
  {t : Complex}
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (weight : Sym2 V -> Complex) :
-- imply
  (surfaceSpinScalePolynomial G edgeClass lambda weight).eval t = surfaceQuadraticEvenPolynomial G edgeClass lambda (fun edge => t * weight edge) := by
-- proof
  apply StatMech.FrontierA.surfaceSpinScalePolynomial_eval G edgeClass lambda weight t

/--
[surface_kacWard_shifted_det_square_of_cycle_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean)
-/
@[path]
private lemma surface_kacWard_shifted_det_square_of_cycle_phase_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq G.Dart]
  {lambda : SurfaceSpinStructure g}
-- given
  (phase : G.Dart -> G.Dart -> Complex)
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (hlog : KWGraphWeightedCycleLog G phase (surfaceSpinCycleCoefficient edgeClass lambda))
  (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
  (hdeg : ∀ vertex, G.degree vertex <= 3)
  (hnonsquare : ∀ m : Sym2 V →₀ Nat, ¬ ons_IsSquarefreeExponent m -> MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0)
  (weight : Sym2 V -> Complex) :
-- imply
  (1 - kwGraphTransition G weight phase).det = surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
-- proof
  apply StatMech.FrontierA.surface_kacWard_shifted_det_square_of_cycle_phase G phase edgeClass lambda hlog hisotropic hdeg hnonsquare weight

/--
[kwGraphFormalLogCoeff_cycle_of_shifted_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean)
-/
@[path]
private lemma kwGraphFormalLogCoeff_cycle_of_shifted_phase_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {lambda : SurfaceSpinStructure g}
  {root : V}
  {p : G.Walk root root}
-- given
  (phase : G.Dart -> G.Dart -> Complex)
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (hrev : KWGraphLoopReversalInvariant G phase)
  (hdeg : ∀ vertex, G.degree vertex <= 3)
  (hp : p.IsCycle)
  (hphase : letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ kwLoopPhaseProduct phase (kwGraphCycleDartLoop p) = -surfaceSpinCycleCoefficient edgeClass lambda p.edges.toFinset) :
-- imply
  kwGraphFormalLogCoeff G phase (ons_finsetExponent p.edges.toFinset) = surfaceSpinCycleCoefficient edgeClass lambda p.edges.toFinset := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLogCoeff_cycle_of_shifted_phase G phase edgeClass lambda hrev hdeg p hp hphase

/--
[kwGraphWeightedCycleLog_of_shifted_simpleCyclePhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean)
-/
@[path]
private lemma kwGraphWeightedCycleLog_of_shifted_simpleCyclePhase_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {lambda : SurfaceSpinStructure g}
-- given
  (phase : G.Dart -> G.Dart -> Complex)
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (hrev : KWGraphLoopReversalInvariant G phase)
  (hdeg : ∀ vertex, G.degree vertex <= 3)
  (hphase : KWGraphShiftedSimpleCyclePhase G phase edgeClass lambda) :
-- imply
  KWGraphWeightedCycleLog G phase (surfaceSpinCycleCoefficient edgeClass lambda) := by
-- proof
  apply StatMech.FrontierA.kwGraphWeightedCycleLog_of_shifted_simpleCyclePhase G phase edgeClass lambda hrev hdeg hphase

/--
[surface_kacWard_shifted_det_square_of_simpleCyclePhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean)
-/
@[path]
private lemma surface_kacWard_shifted_det_square_of_simpleCyclePhase_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq G.Dart]
  {lambda : SurfaceSpinStructure g}
-- given
  (phase : G.Dart -> G.Dart -> Complex)
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (hrev : KWGraphLoopReversalInvariant G phase)
  (hphase : KWGraphShiftedSimpleCyclePhase G phase edgeClass lambda)
  (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
  (hdeg : ∀ vertex, G.degree vertex <= 3)
  (hnonsquare : ∀ m : Sym2 V →₀ Nat, ¬ ons_IsSquarefreeExponent m -> MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0)
  (weight : Sym2 V -> Complex) :
-- imply
  (1 - kwGraphTransition G weight phase).det = surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
-- proof
  apply StatMech.FrontierA.surface_kacWard_shifted_det_square_of_simpleCyclePhase G phase edgeClass lambda hrev hphase hisotropic hdeg hnonsquare weight

/--
[kwAngularSplit_shifted_det_square_of_cyclePhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean)
-/
@[path]
private lemma kwAngularSplit_shifted_det_square_of_cyclePhase_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {lambda : SurfaceSpinStructure 1}
-- given
  (edgeClass : Sym2 (KWDartPort G) -> SurfaceHomology 1)
  (hphase : KWAngularSplitShiftedCyclePhase embedding edgeClass lambda)
  (hisotropic : SurfaceDisjointCycleIsotropic (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) edgeClass)
  (weight : Sym2 (KWDartPort G) -> Complex) :
-- imply
  (1 - kwGraphTransition (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) weight (kwAngularSplitPhase embedding)).det = surfaceQuadraticEvenPolynomial (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) edgeClass lambda weight ^ 2 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_shifted_det_square_of_cyclePhase embedding edgeClass lambda hphase hisotropic weight

/--
[surface_kacWard_original_of_angularSplit_shifted_cyclePhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean)
-/
@[path]
private lemma surface_kacWard_original_of_angularSplit_shifted_cyclePhase_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {lambda : SurfaceSpinStructure 1}
-- given
  (edgeClass : Sym2 V -> SurfaceHomology 1)
  (hdiag : ∀ v, edgeClass s(v, v) = 0)
  (weight : Sym2 V -> Complex)
  (hphase : KWAngularSplitShiftedCyclePhase embedding (kwOrderedSplitEdgeClass edgeClass) lambda)
  (hisotropic : SurfaceDisjointCycleIsotropic (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwOrderedSplitEdgeClass edgeClass)) :
-- imply
  (1 - kwGraphTransition G weight embedding.turnPhase).det = surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
-- proof
  apply StatMech.FrontierA.surface_kacWard_original_of_angularSplit_shifted_cyclePhase embedding edgeClass hdiag lambda weight hphase hisotropic

/--
[kwLocalAngularSplit_shifted_det_square_of_cyclePhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean)
-/
@[path]
private lemma kwLocalAngularSplit_shifted_det_square_of_cyclePhase_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {lambda : SurfaceSpinStructure 1}
-- given
  (edgeClass : Sym2 (KWDartPort G) -> SurfaceHomology 1)
  (hphase : KWLocalAngularSplitShiftedCyclePhase data edgeClass lambda)
  (hisotropic : SurfaceDisjointCycleIsotropic (kwOrderedDartPortSplitGraph G data.order) edgeClass)
  (weight : Sym2 (KWDartPort G) -> Complex) :
-- imply
  (1 - kwGraphTransition (kwOrderedDartPortSplitGraph G data.order) weight (kwLocalAngularSplitPhase data)).det = surfaceQuadraticEvenPolynomial (kwOrderedDartPortSplitGraph G data.order) edgeClass lambda weight ^ 2 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_shifted_det_square_of_cyclePhase data edgeClass lambda hphase hisotropic weight

/--
[surface_kacWard_original_of_localAngularSplit_shifted_cyclePhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean)
-/
@[path]
private lemma surface_kacWard_original_of_localAngularSplit_shifted_cyclePhase_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {lambda : SurfaceSpinStructure 1}
-- given
  (edgeClass : Sym2 V -> SurfaceHomology 1)
  (hdiag : forall v, edgeClass s(v, v) = 0)
  (weight : Sym2 V -> Complex)
  (hphase : KWLocalAngularSplitShiftedCyclePhase data (kwOrderedSplitEdgeClass edgeClass) lambda)
  (hisotropic : SurfaceDisjointCycleIsotropic (kwOrderedDartPortSplitGraph G data.order) (kwOrderedSplitEdgeClass edgeClass)) :
-- imply
  (1 - kwGraphTransition G weight data.phase).det = surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
-- proof
  apply StatMech.FrontierA.surface_kacWard_original_of_localAngularSplit_shifted_cyclePhase data edgeClass hdiag lambda weight hphase hisotropic


-- created on 2026-10-23
