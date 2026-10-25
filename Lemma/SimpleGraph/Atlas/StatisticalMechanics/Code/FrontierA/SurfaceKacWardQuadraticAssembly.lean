import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardQuadraticAssembly.Part4
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[kwWeightedCycleComponentSeries_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma kwWeightedCycleComponentSeries_coeff_eq
  {V I : Type u}
  [DecidableEq V]
  [Fintype I]
  {G : SimpleGraph V}
  {m : Sym2 V →₀ Nat}
-- given
  (base : I -> V)
  (cycle : (i : I) -> G.Walk (base i) (base i))
  (coefficient : I -> Complex) :
-- imply
  MvPowerSeries.coeff m (kwWeightedCycleComponentSeries base cycle coefficient) = ∑ i : I, if ons_finsetExponent (cycle i).edges.toFinset = m then coefficient i else 0 := by
-- proof
  apply StatMech.FrontierA.kwWeightedCycleComponentSeries_coeff base cycle coefficient m

/--
[kwWeightedCycleComponentSeries_coeff_piece](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma kwWeightedCycleComponentSeries_coeff_piece_eq
  {V I : Type u}
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {j : I}
-- given
  (base : I -> V)
  (cycle : (i : I) -> G.Walk (base i) (base i))
  (coefficient : I -> Complex)
  (hcycle : forall i, (cycle i).IsCycle)
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i => (cycle i).edges.toFinset)) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent (cycle j).edges.toFinset) (kwWeightedCycleComponentSeries base cycle coefficient) = coefficient j := by
-- proof
  apply StatMech.FrontierA.kwWeightedCycleComponentSeries_coeff_piece base cycle coefficient hcycle hdisj j

/--
[kwWeightedCycleComponentSeries_hasSubst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma kwWeightedCycleComponentSeries_hasSubst_eq
  {V I : Type u}
  [DecidableEq V]
  [Fintype I]
  {G : SimpleGraph V}
-- given
  (base : I -> V)
  (cycle : (i : I) -> G.Walk (base i) (base i))
  (coefficient : I -> Complex)
  (hcycle : forall i, (cycle i).IsCycle) :
-- imply
  PowerSeries.HasSubst (kwWeightedCycleComponentSeries base cycle coefficient) := by
-- proof
  apply StatMech.FrontierA.kwWeightedCycleComponentSeries_hasSubst base cycle coefficient hcycle

/--
[kwGraphFormalLog_coeff_eq_weightedCycleComponent_of_antidiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma kwGraphFormalLog_coeff_eq_weightedCycleComponent_of_antidiag_eq
  {V I : Type u}
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  [DecidableEq K]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset (Sym2 V)}
  {T : Finset K}
  {g : K →₀ Sym2 V →₀ Nat}
  {i : K}
-- given
  (phase : G.Dart -> G.Dart -> Complex)
  (cycleCoeff : Finset (Sym2 V) -> Complex)
  (hlog : KWGraphWeightedCycleLog G phase cycleCoeff)
  (hdeg : forall vertex, G.degree vertex <= 3)
  (hS : S ∈ evenSubgraphs G)
  (base : I -> V)
  (cycle : (i : I) -> G.Walk (base i) (base i))
  (hcycle : forall i, (cycle i).IsCycle)
  (hcover : S = Finset.univ.biUnion (fun i => (cycle i).edges.toFinset))
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i => (cycle i).edges.toFinset))
  (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
  (hi : i ∈ T) :
-- imply
  kwGraphFormalLogCoeff G phase (g i) = MvPowerSeries.coeff (g i) (kwWeightedCycleComponentSeries base cycle (fun j => cycleCoeff (cycle j).edges.toFinset)) := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLog_coeff_eq_weightedCycleComponent_of_antidiag G phase cycleCoeff hlog hdeg S hS base cycle hcycle hcover hdisj T g hg hi

/--
[kwWeightedCycleComponentSeries_pow_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma kwWeightedCycleComponentSeries_pow_coeff_eq
  {V I : Type u}
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {S : Finset (Sym2 V)}
  {n : Nat}
-- given
  (base : I -> V)
  (cycle : (i : I) -> G.Walk (base i) (base i))
  (coefficient : I -> Complex)
  (hcycle : forall i, (cycle i).IsCycle)
  (hcover : S = Finset.univ.biUnion (fun i => (cycle i).edges.toFinset))
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i => (cycle i).edges.toFinset)) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) ((kwWeightedCycleComponentSeries base cycle coefficient) ^ n) = if n = Fintype.card I then (n.factorial : Complex) * ∏ i, coefficient i else 0 := by
-- proof
  apply StatMech.FrontierA.kwWeightedCycleComponentSeries_pow_coeff S base cycle coefficient hcycle hcover hdisj n

/--
[kwWeightedCycleComponentExp_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma kwWeightedCycleComponentExp_coeff_eq
  {V I : Type u}
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {S : Finset (Sym2 V)}
-- given
  (base : I -> V)
  (cycle : (i : I) -> G.Walk (base i) (base i))
  (coefficient : I -> Complex)
  (hcycle : forall i, (cycle i).IsCycle)
  (hcover : S = Finset.univ.biUnion (fun i => (cycle i).edges.toFinset))
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i => (cycle i).edges.toFinset)) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) (PowerSeries.subst (kwWeightedCycleComponentSeries base cycle coefficient) (PowerSeries.exp Complex)) = ∏ i, coefficient i := by
-- proof
  apply StatMech.FrontierA.kwWeightedCycleComponentExp_coeff S base cycle coefficient hcycle hcover hdisj

/--
[kwGraphFormalRoot_coeff_evenSubgraph_of_weightedCycleLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma kwGraphFormalRoot_coeff_evenSubgraph_of_weightedCycleLog_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset (Sym2 V)}
-- given
  (phase : G.Dart -> G.Dart -> Complex)
  (cycleCoeff : Finset (Sym2 V) -> Complex)
  (hlog : KWGraphWeightedCycleLog G phase cycleCoeff)
  (hdeg : forall vertex, G.degree vertex <= 3)
  (hS : S ∈ evenSubgraphs G) :
-- imply
  exists (I : Type u) (_ : Fintype I) (_ : DecidableEq I) (base : I -> V) (cycle : (i : I) -> G.Walk (base i) (base i)), (forall i, (cycle i).IsCycle) /\ S = Finset.univ.biUnion (fun i => (cycle i).edges.toFinset) /\ ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i => (cycle i).edges.toFinset) /\ ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i => (cycle i).toSubgraph.verts) /\ MvPowerSeries.coeff (ons_finsetExponent S) (kwGraphFormalRoot G phase) = ∏ i, cycleCoeff (cycle i).edges.toFinset := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_coeff_evenSubgraph_of_weightedCycleLog G phase cycleCoeff hlog hdeg S hS

/--
[surfaceIntersection_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma surfaceIntersection_add_right_eq
  {g : Nat}
-- given
  (h k l : SurfaceHomology g) :
-- imply
  surfaceIntersection h (k + l) = surfaceIntersection h k + surfaceIntersection h l := by
-- proof
  apply StatMech.FrontierA.surfaceIntersection_add_right h k l

/--
[surfaceIntersection_finset_sum_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma surfaceIntersection_finset_sum_right_eq
  {g : Nat}
  [DecidableEq I]
  {S : Finset I}
-- given
  (h : SurfaceHomology g)
  (f : I -> SurfaceHomology g) :
-- imply
  surfaceIntersection h (∑ i ∈ S, f i) = ∑ i ∈ S, surfaceIntersection h (f i) := by
-- proof
  apply StatMech.FrontierA.surfaceIntersection_finset_sum_right h S f

/--
[surfaceQuadraticParity_finset_sum_of_pairwise_intersection_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma surfaceQuadraticParity_finset_sum_of_pairwise_intersection_zero_eq
  {g : Nat}
  [DecidableEq I]
  {lambda : SurfaceSpinStructure g}
  {S : Finset I}
-- given
  (f : I -> SurfaceHomology g)
  (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j -> surfaceIntersection (f i) (f j) = 0) :
-- imply
  surfaceQuadraticParity lambda (∑ i ∈ S, f i) = ∑ i ∈ S, surfaceQuadraticParity lambda (f i) := by
-- proof
  apply StatMech.FrontierA.surfaceQuadraticParity_finset_sum_of_pairwise_intersection_zero lambda S f hpair

/--
[surfaceParitySign_quadratic_finset_sum_of_pairwise_intersection_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma surfaceParitySign_quadratic_finset_sum_of_pairwise_intersection_zero_eq
  {g : Nat}
  [DecidableEq I]
  {lambda : SurfaceSpinStructure g}
  {S : Finset I}
-- given
  (f : I -> SurfaceHomology g)
  (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j -> surfaceIntersection (f i) (f j) = 0) :
-- imply
  (surfaceParitySign (surfaceQuadraticParity lambda (∑ i ∈ S, f i)) : Complex) = ∏ i ∈ S, (surfaceParitySign (surfaceQuadraticParity lambda (f i)) : Complex) := by
-- proof
  apply StatMech.FrontierA.surfaceParitySign_quadratic_finset_sum_of_pairwise_intersection_zero lambda S f hpair

/--
[surfaceSubgraphHomology_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma surfaceSubgraphHomology_biUnion_eq
  {g : Nat}
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {S : Finset (Sym2 V)}
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (piece : I -> Finset (Sym2 V))
  (hcover : S = Finset.univ.biUnion piece)
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint piece) :
-- imply
  surfaceSubgraphHomology edgeClass S = ∑ i, surfaceSubgraphHomology edgeClass (piece i) := by
-- proof
  apply StatMech.FrontierA.surfaceSubgraphHomology_biUnion edgeClass S piece hcover hdisj

/--
[kwGraphFormalRoot_coeff_surfaceQuadratic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma kwGraphFormalRoot_coeff_surfaceQuadratic_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset (Sym2 V)}
-- given
  (phase : G.Dart -> G.Dart -> Complex)
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (hlog : KWGraphWeightedCycleLog G phase (surfaceBaseCycleCoefficient edgeClass))
  (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
  (hdeg : forall vertex, G.degree vertex <= 3)
  (hS : S ∈ evenSubgraphs G) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) (kwGraphFormalRoot G phase) = (surfaceParitySign (surfaceBaseQuadraticParity (surfaceSubgraphHomology edgeClass S)) : Complex) := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_coeff_surfaceQuadratic G phase edgeClass hlog hisotropic hdeg S hS

/--
[kwGraphFormalRoot_coeff_squarefree_eq_zero_of_not_even_weighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma kwGraphFormalRoot_coeff_squarefree_eq_zero_of_not_even_weighted_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset (Sym2 V)}
-- given
  (phase : G.Dart -> G.Dart -> Complex)
  (cycleCoeff : Finset (Sym2 V) -> Complex)
  (hlog : KWGraphWeightedCycleLog G phase cycleCoeff)
  (hS : S ∉ evenSubgraphs G) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) (kwGraphFormalRoot G phase) = 0 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_coeff_squarefree_eq_zero_of_not_even_weighted G phase cycleCoeff hlog S hS

/--
[surfaceBaseFormalEvenPolynomial_eq_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma surfaceBaseFormalEvenPolynomial_eq_coe_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g) :
-- imply
  surfaceBaseFormalEvenPolynomial G edgeClass = (surfaceBaseEvenMvPolynomial G edgeClass : MvPowerSeries (Sym2 V) Complex) := by
-- proof
  apply StatMech.FrontierA.surfaceBaseFormalEvenPolynomial_eq_coe G edgeClass

/--
[surfaceBaseFormalEvenPolynomial_coeff_finsetExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma surfaceBaseFormalEvenPolynomial_coeff_finsetExponent_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset (Sym2 V)}
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) (surfaceBaseFormalEvenPolynomial G edgeClass) = if S ∈ evenSubgraphs G then surfaceBaseCycleCoefficient edgeClass S else 0 := by
-- proof
  apply StatMech.FrontierA.surfaceBaseFormalEvenPolynomial_coeff_finsetExponent G edgeClass S

/--
[surfaceBaseFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma surfaceBaseFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Sym2 V →₀ Nat}
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (hm : ¬ ons_IsSquarefreeExponent m) :
-- imply
  MvPowerSeries.coeff m (surfaceBaseFormalEvenPolynomial G edgeClass) = 0 := by
-- proof
  apply StatMech.FrontierA.surfaceBaseFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree G edgeClass m hm

/--
[kwGraphFormalRoot_eq_surfaceBaseFormalEvenPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma kwGraphFormalRoot_eq_surfaceBaseFormalEvenPolynomial_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (phase : G.Dart -> G.Dart -> Complex)
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (hlog : KWGraphWeightedCycleLog G phase (surfaceBaseCycleCoefficient edgeClass))
  (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
  (hdeg : ∀ vertex, G.degree vertex <= 3)
  (hnonsquare : ∀ m : Sym2 V →₀ Nat, ¬ ons_IsSquarefreeExponent m -> MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0) :
-- imply
  kwGraphFormalRoot G phase = surfaceBaseFormalEvenPolynomial G edgeClass := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_eq_surfaceBaseFormalEvenPolynomial G phase edgeClass hlog hisotropic hdeg hnonsquare

/--
[surfaceBaseEvenMvPolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma surfaceBaseEvenMvPolynomial_eval_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (weight : Sym2 V -> Complex) :
-- imply
  MvPolynomial.eval weight (surfaceBaseEvenMvPolynomial G edgeClass) = surfaceQuadraticEvenPolynomial G edgeClass (0 : SurfaceSpinStructure g) weight := by
-- proof
  apply StatMech.FrontierA.surfaceBaseEvenMvPolynomial_eval G edgeClass weight

/--
[surfaceBaseFormalEvenPolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma surfaceBaseFormalEvenPolynomial_eval_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (weight : Sym2 V -> Complex) :
-- imply
  ons_mvSeriesEval (surfaceBaseFormalEvenPolynomial G edgeClass) weight = surfaceQuadraticEvenPolynomial G edgeClass (0 : SurfaceSpinStructure g) weight := by
-- proof
  apply StatMech.FrontierA.surfaceBaseFormalEvenPolynomial_eval G edgeClass weight

/--
[surfaceBaseScalePolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma surfaceBaseScalePolynomial_eval_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {t : Complex}
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (weight : Sym2 V -> Complex) :
-- imply
  (surfaceBaseScalePolynomial G edgeClass weight).eval t = surfaceQuadraticEvenPolynomial G edgeClass (0 : SurfaceSpinStructure g) (fun edge => t * weight edge) := by
-- proof
  apply StatMech.FrontierA.surfaceBaseScalePolynomial_eval G edgeClass weight t

/--
[surface_kacWard_base_det_square_of_cycle_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma surface_kacWard_base_det_square_of_cycle_phase_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq G.Dart]
-- given
  (phase : G.Dart -> G.Dart -> Complex)
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (hlog : KWGraphWeightedCycleLog G phase (surfaceBaseCycleCoefficient edgeClass))
  (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
  (hdeg : ∀ vertex, G.degree vertex <= 3)
  (hnonsquare : ∀ m : Sym2 V →₀ Nat, ¬ ons_IsSquarefreeExponent m -> MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0)
  (weight : Sym2 V -> Complex) :
-- imply
  (1 - kwGraphTransition G weight phase).det = surfaceQuadraticEvenPolynomial G edgeClass (0 : SurfaceSpinStructure g) weight ^ 2 := by
-- proof
  apply StatMech.FrontierA.surface_kacWard_base_det_square_of_cycle_phase G phase edgeClass hlog hisotropic hdeg hnonsquare weight

/--
[surface_twisted_kacWard_det_square_of_cycle_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma surface_twisted_kacWard_det_square_of_cycle_phase_eq
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
  (hlog : KWGraphWeightedCycleLog G phase (surfaceBaseCycleCoefficient edgeClass))
  (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
  (hdeg : ∀ vertex, G.degree vertex <= 3)
  (hnonsquare : ∀ m : Sym2 V →₀ Nat, ¬ ons_IsSquarefreeExponent m -> MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0)
  (weight : Sym2 V -> Complex) :
-- imply
  (1 - surfaceTwistedKacWardMatrix G phase edgeClass lambda weight).det = surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
-- proof
  apply StatMech.FrontierA.surface_twisted_kacWard_det_square_of_cycle_phase G phase edgeClass hlog hisotropic hdeg hnonsquare lambda weight

/--
[surface_twisted_kacWard_det_eq_sectorSquare_of_cycle_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean)
-/
@[path]
private lemma surface_twisted_kacWard_det_eq_sectorSquare_of_cycle_phase_eq
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
  (hlog : KWGraphWeightedCycleLog G phase (surfaceBaseCycleCoefficient edgeClass))
  (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
  (hdeg : ∀ vertex, G.degree vertex <= 3)
  (hnonsquare : ∀ m : Sym2 V →₀ Nat, ¬ ons_IsSquarefreeExponent m -> MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0)
  (weight : Sym2 V -> Real) :
-- imply
  (1 - surfaceTwistedKacWardMatrix G phase edgeClass lambda (fun edge => (weight edge : Complex))).det = (surfaceTwistedSectorSquare (surfaceGraphSectorWeight G edgeClass weight) lambda : Complex) := by
-- proof
  apply StatMech.FrontierA.surface_twisted_kacWard_det_eq_sectorSquare_of_cycle_phase G phase edgeClass hlog hisotropic hdeg hnonsquare lambda weight


-- created on 2026-10-23
