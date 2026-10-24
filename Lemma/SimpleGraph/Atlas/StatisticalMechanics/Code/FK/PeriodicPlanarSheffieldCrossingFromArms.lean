import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrossingFromArms
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.exists_boundary_walk_of_walk_to_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrossingFromArms.lean)
-/
@[path]
private lemma exists_boundary_walk_of_walk_to_compl_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {A : Set V}
  {x y : V}
  {p : (P.openSubgraph omega).Walk x y}
-- given
  (hx : x ∈ A)
  (hy : y ∉ A) :
-- imply
  ∃ b ∈ A, ∃ z : V, P.graph.Adj b z ∧ z ∉ A ∧ ∃ q : (P.openSubgraph omega).Walk x b, (∀ v ∈ q.support, v ∈ A) ∧ ∀ v ∈ q.support, v ∈ p.support := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_boundary_walk_of_walk_to_compl P omega A p hx hy

/--
[PeriodicPlaneEmbedding.openSub_rectRestrict_eq_induce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrossingFromArms.lean)
-/
@[path]
private lemma openSub_rectRestrict_eq_induce_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  FK.openSub (E.rectGraph a b c d) (E.rectRestrict a b c d omega) = (P.openSubgraph omega).induce (E.rectVertices a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.openSub_rectRestrict_eq_induce E a b c d omega

/--
[PeriodicPlaneEmbedding.verticalCrossingEvent_mono_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrossingFromArms.lean)
-/
@[path]
private lemma verticalCrossingEvent_mono_right_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b b' c d : Real}
-- given
  (hbb' : b ≤ b') :
-- imply
  E.verticalCrossingEvent a b c d ⊆ E.verticalCrossingEvent a b' c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossingEvent_mono_right E hbb'

/--
[PeriodicPlaneEmbedding.verticalCrossing_measureReal_mono_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrossingFromArms.lean)
-/
@[path]
private lemma verticalCrossing_measureReal_mono_right_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {a b b' c d : Real}
-- given
  (hbb' : b ≤ b') :
-- imply
  mu.real (E.verticalCrossingEvent a b c d) ≤ mu.real (E.verticalCrossingEvent a b' c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossing_measureReal_mono_right E mu hbb'

/--
[PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_subset_verticalCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrossingFromArms.lean)
-/
@[path]
private lemma finiteStripJoinedBoundaryArmEvent_subset_verticalCrossing_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {B r c d : Real}
  {n : Nat}
  {L R : Finset V}
-- given
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hB0 : 0 ≤ B)
  (hgap : 3 * B < d - c) :
-- imply
  E.finiteStripJoinedBoundaryArmEvent r c d n L R ⊆ E.verticalCrossingEvent r (r + n) ((2 * c + d) / 3) ((c + 2 * d) / 3) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_subset_verticalCrossing E hB hB0 hgap

/--
[PeriodicPlaneEmbedding.verticalCrossing_tendsto_one_of_finiteStripJoinedBoundaryArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrossingFromArms.lean)
-/
@[path]
private lemma verticalCrossing_tendsto_one_of_finiteStripJoinedBoundaryArms_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {r c d : Nat → Real}
  {width : Nat → Nat}
  {lower upper : Nat → Finset V}
-- given
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxy u - E.vertex x) i| ≤ B)
  (hB0 : 0 ≤ B)
  (hgap : ∀ n, 3 * B < d n - c n)
  (harms : Tendsto (fun n ↦ mu.real (E.finiteStripJoinedBoundaryArmEvent (r n) (c n) (d n) (width n) (lower n) (upper n))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n ↦ mu.real (E.verticalCrossingEvent (r n) (r n + width n) ((2 * c n + d n) / 3) ((c n + 2 * d n) / 3))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossing_tendsto_one_of_finiteStripJoinedBoundaryArms E mu B hB hB0 r c d width lower upper hgap harms

/--
[PeriodicPlaneEmbedding.exists_verticalCrossing_measureReal_gt_of_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrossingFromArms.lean)
-/
@[path]
private lemma exists_verticalCrossing_measureReal_gt_of_unique_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r B s : Real}
  {t : Int}
  {m : Nat}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hB0 : 0 ≤ B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxy u - E.vertex x) i| ≤ B)
  (ht : 3 * B < t)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ n : Nat, m ≤ n ∧ 1 - epsilon < mu.real (E.verticalCrossingEvent r (r + n) ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_verticalCrossing_measureReal_gt_of_unique E mu hFKG hTI hunique r B s hB0 hB t ht m hepsilon

/--
[PeriodicPlaneEmbedding.exists_cofinal_verticalCrossing_tendsto_one_of_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrossingFromArms.lean)
-/
@[path]
private lemma exists_cofinal_verticalCrossing_tendsto_one_of_unique_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r B s : Real}
  {t : Int}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hB0 : 0 ≤ B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxy u - E.vertex x) i| ≤ B)
  (ht : 3 * B < t) :
-- imply
  ∃ width : Nat → Nat, Tendsto width atTop atTop ∧ Tendsto (fun k => mu.real (E.verticalCrossingEvent r (r + width k) ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_cofinal_verticalCrossing_tendsto_one_of_unique E mu hFKG hTI hunique r B s hB0 hB t ht

/--
[PeriodicPlanarDualPair.exists_cofinal_complementaryDual_verticalCrossing_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrossingFromArms.lean)
-/
@[path]
private lemma exists_cofinal_complementaryDual_verticalCrossing_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {Pdual : PeriodicGraph W}
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r B s : Real}
  {t : Int}
-- given
  (hdualFKG : IsFKG (D.dualMeasure mu))
  (hTI : P.IsTranslationInvariant mu)
  (hdualUnique : D.dualMeasure mu {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hB0 : 0 ≤ B)
  (hB : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy u - D.dualEmbedding.vertex x) i| ≤ B)
  (ht : 3 * B < t) :
-- imply
  ∃ width : Nat → Nat, Tendsto width atTop atTop ∧ Tendsto (fun k => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent r (r + width k) ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_cofinal_complementaryDual_verticalCrossing_tendsto_one D mu hdualFKG hTI hdualUnique r B s hB0 hB t ht


-- created on 2026-10-23
