import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArms.Part2
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[walkOfChain_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma walkOfChain_support_eq
  [DecidableEq V]
  [Countable V]
  {G : SimpleGraph V}
  {x : V}
  {l : List V}
-- given
  (h : List.IsChain G.Adj (x :: l)) :
-- imply
  (walkOfChain G x l h).support = x :: l := by
-- proof
  apply StatMech.FK.PeriodicPlanar.walkOfChain_support G x l h

/--
[PeriodicGraph.connectedWithinSet_exists_openSubgraphWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma connectedWithinSet_exists_openSubgraphWalk_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {A : Set V}
  {x y : V}
-- given
  (h : omega ∈ P.connectedWithinSet A x y) :
-- imply
  ∃ q : (P.openSubgraph omega).Walk x y, ∀ v ∈ q.support, v ∈ A := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.connectedWithinSet_exists_openSubgraphWalk P h

/--
[PeriodicGraph.openSubgraphWalk_exists_graphWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma openSubgraphWalk_exists_graphWalk_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V}
  {q : (P.openSubgraph omega).Walk x y} :
-- imply
  ∃ qG : P.graph.Walk x y, qG.support = q.support ∧ ∀ {u v : V}, s(u, v) ∈ qG.edges → omega s(u, v) = true := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.openSubgraphWalk_exists_graphWalk P omega q

/--
[PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmEvent_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V} :
-- imply
  MeasurableSet (E.finiteJoinedBoundaryArmEvent r c d n L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_measurableSet E r c d n L R

/--
[PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmEvent_witnesses_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V}
-- given
  (h : omega ∈ E.finiteJoinedBoundaryArmEvent r c d n L R) :
-- imply
  ∃ x ∈ L, (P.cluster omega x).Infinite ∧ ∃ b ∈ E.lowerBoundaryRayVertices r c, omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b ∧ ∃ y ∈ R, (P.cluster omega y).Infinite ∧ ∃ u ∈ E.upperBoundaryRayVertices r d, omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) y u ∧ omega ∈ P.connectedWithinSet (E.rightHalfPlaneStripVertices r n) x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_witnesses E h

/--
[PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_openWalks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmEvent_openWalks_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V}
-- given
  (h : omega ∈ E.finiteJoinedBoundaryArmEvent r c d n L R) :
-- imply
  ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ j : V, ∃ lower : (P.openSubgraph omega).Walk b j, ∃ upper : (P.openSubgraph omega).Walk u j, j ∈ L ∧ (∀ v ∈ lower.support, v ∈ E.rightHalfPlaneVertices r) ∧ (∀ v ∈ upper.support, v ∈ E.rightHalfPlaneVertices r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_openWalks E h

/--
[PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_threeWallWalks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmEvent_threeWallWalks_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V}
-- given
  (h : omega ∈ E.finiteJoinedBoundaryArmEvent r c d n L R) :
-- imply
  ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ x ∈ L, ∃ y ∈ R, ∃ lower : P.graph.Walk b x, ∃ right : P.graph.Walk x y, ∃ upper : P.graph.Walk y u, (∀ {v w : V}, s(v, w) ∈ lower.edges → omega s(v, w) = true) ∧ (∀ {v w : V}, s(v, w) ∈ right.edges → omega s(v, w) = true) ∧ (∀ {v w : V}, s(v, w) ∈ upper.edges → omega s(v, w) = true) ∧ (∀ v ∈ lower.support, v ∈ E.rightHalfPlaneVertices r) ∧ (∀ v ∈ right.support, v ∈ E.rightHalfPlaneStripVertices r n) ∧ ∀ v ∈ upper.support, v ∈ E.rightHalfPlaneVertices r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_threeWallWalks E h

/--
[PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_threeWallCrosscutWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmEvent_threeWallCrosscutWalk_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V}
-- given
  (hcd : c < d)
  (h : omega ∈ E.finiteJoinedBoundaryArmEvent r c d n L R) :
-- imply
  ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ x ∈ L, ∃ y ∈ R, ∃ p : P.graph.Walk b u, ¬ p.Nil ∧ (∀ {v w : V}, s(v, w) ∈ p.edges → omega s(v, w) = true) ∧ (∀ v ∈ p.support, v ∈ E.rightHalfPlaneVertices r) ∧ x ∈ p.support ∧ y ∈ p.support := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_threeWallCrosscutWalk E hcd h

/--
[PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_graphWalks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmEvent_graphWalks_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V}
-- given
  (h : omega ∈ E.finiteJoinedBoundaryArmEvent r c d n L R) :
-- imply
  ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ j : V, ∃ lower : P.graph.Walk b j, ∃ upper : P.graph.Walk u j, j ∈ L ∧ (∀ {x y : V}, s(x, y) ∈ lower.edges → omega s(x, y) = true) ∧ (∀ {x y : V}, s(x, y) ∈ upper.edges → omega s(x, y) = true) ∧ (∀ v ∈ lower.support, v ∈ E.rightHalfPlaneVertices r) ∧ (∀ v ∈ upper.support, v ∈ E.rightHalfPlaneVertices r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_graphWalks E h

/--
[PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_graphWalks_notNil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmEvent_graphWalks_notNil_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {B r c d : Real}
  {n : Nat}
  {L R : Finset V}
-- given
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hLdeep : (L : Set V) ⊆ E.rightHalfPlaneVertices (r + B))
  (h : omega ∈ E.finiteJoinedBoundaryArmEvent r c d n L R) :
-- imply
  ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ j : V, ∃ lower : P.graph.Walk b j, ∃ upper : P.graph.Walk u j, ¬ lower.Nil ∧ ¬ upper.Nil ∧ (∀ {x y : V}, s(x, y) ∈ lower.edges → omega s(x, y) = true) ∧ (∀ {x y : V}, s(x, y) ∈ upper.edges → omega s(x, y) = true) ∧ (∀ v ∈ lower.support, v ∈ E.rightHalfPlaneVertices r) ∧ (∀ v ∈ upper.support, v ∈ E.rightHalfPlaneVertices r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_graphWalks_notNil E hB hLdeep h

/--
[PeriodicPlaneEmbedding.exists_walkArc_horizontal_strict_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma exists_walkArc_horizontal_strict_bounds_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {x y z : V}
  {lower : P.graph.Walk x z}
  {upper : P.graph.Walk y z} :
-- imply
  ∃ a b : Real, a < b ∧ (∀ t : unitInterval, a < E.coordinates (E.walkArc lower t) 0 ∧ E.coordinates (E.walkArc lower t) 0 < b) ∧ (∀ t : unitInterval, a < E.coordinates (E.walkArc upper t) 0 ∧ E.coordinates (E.walkArc upper t) 0 < b) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_walkArc_horizontal_strict_bounds E lower upper

/--
[PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_barrierReady](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmEvent_barrierReady_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {B r c d : Real}
  {n : Nat}
  {L R : Finset V}
-- given
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hcd : c < d)
  (hLdeep : (L : Set V) ⊆ E.rightHalfPlaneVertices (r + B))
  (h : omega ∈ E.finiteJoinedBoundaryArmEvent r c d n L R) :
-- imply
  ∃ a b C D : Real, a < b ∧ C < D ∧ ∃ xl xu xj : V, ∃ lower : P.graph.Walk xl xj, ∃ upper : P.graph.Walk xu xj, ¬ lower.Nil ∧ ¬ upper.Nil ∧ (∀ {x y : V}, s(x, y) ∈ lower.edges → omega s(x, y) = true) ∧ (∀ {x y : V}, s(x, y) ∈ upper.edges → omega s(x, y) = true) ∧ E.vertexCoord xl 1 < C ∧ D < E.vertexCoord xu 1 ∧ (∀ t : unitInterval, a < E.coordinates (E.walkArc lower t) 0 ∧ E.coordinates (E.walkArc lower t) 0 < b) ∧ (∀ t : unitInterval, a < E.coordinates (E.walkArc upper t) 0 ∧ E.coordinates (E.walkArc upper t) 0 < b) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_barrierReady E hB hcd hLdeep h

/--
[PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_measureReal_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmEvent_measureReal_ge_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r c d : Real}
  {n : Nat}
  {L R : Finset V} :
-- imply
  mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (L : Set V) (E.lowerBoundaryRayVertices r c)) + mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (R : Set V) (E.upperBoundaryRayVertices r d)) - mu.real (E.halfPlaneStripPairMergeErrorUnion r n L R) - 1 ≤ mu.real (E.finiteJoinedBoundaryArmEvent r c d n L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_measureReal_ge E mu r c d n L R

/--
[PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_measureReal_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmEvent_measureReal_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r c d : Real}
  {n : Nat}
  {L R : Finset V}
  {epsilon : Real}
-- given
  (hL : 1 - epsilon < mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (L : Set V) (E.lowerBoundaryRayVertices r c)))
  (hR : 1 - epsilon < mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (R : Set V) (E.upperBoundaryRayVertices r d)))
  (hmerge : mu.real (E.halfPlaneStripPairMergeErrorUnion r n L R) < epsilon) :
-- imply
  1 - 3 * epsilon < mu.real (E.finiteJoinedBoundaryArmEvent r c d n L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_measureReal_gt E mu r c d n L R hL hR hmerge

/--
[PeriodicPlaneEmbedding.exists_inward_finiteJoinedBoundaryArmEvent_measureReal_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma exists_inward_finiteJoinedBoundaryArmEvent_measureReal_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
  {L : Finset V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ z₀ : Site 2, ∃ z : Int, ∃ n : Nat, let S := L.image (P.shift z₀) let Slo := S.image (P.shift (verticalShift z)) let Shi := (S.image (P.shift (verticalShift 1))).image (P.shift (verticalShift z)) 1 - 2 * Real.sqrt (1 - mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (S : Set V) (E.rightHalfPlaneBoundaryVertices r))) - 3 * epsilon < mu.real (E.finiteJoinedBoundaryArmEvent r 0 0 n Slo Shi) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_inward_finiteJoinedBoundaryArmEvent_measureReal_gt E mu hFKG hTI hunique r L hepsilon

/--
[PeriodicPlaneEmbedding.exists_inward_finiteJoinedBoundaryArmEvent_with_margin_measureReal_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma exists_inward_finiteJoinedBoundaryArmEvent_with_margin_measureReal_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R : Real}
  {L : Finset V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : r ≤ R)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ z₀ : Site 2, ∃ z : Int, ∃ n : Nat, let S := L.image (P.shift z₀) let Slo := S.image (P.shift (verticalShift z)) let Shi := (S.image (P.shift (verticalShift 2))).image (P.shift (verticalShift z)) (S : Set V) ⊆ E.rightHalfPlaneVertices R ∧ (Slo : Set V) ⊆ E.rightHalfPlaneVertices R ∧ 1 - 2 * Real.sqrt (1 - mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (S : Set V) (E.rightHalfPlaneBoundaryVertices r))) - 3 * epsilon < mu.real (E.finiteJoinedBoundaryArmEvent r 0 1 n Slo Shi) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_inward_finiteJoinedBoundaryArmEvent_with_margin_measureReal_gt E mu hFKG hTI hunique hrR L hepsilon

/--
[PeriodicPlaneEmbedding.exists_inward_separated_finiteJoinedBoundaryArmEvent_with_margin_measureReal_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean)
-/
@[path]
private lemma exists_inward_separated_finiteJoinedBoundaryArmEvent_with_margin_measureReal_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R : Real}
  {s : Real}
  {t : Int}
  {L : Finset V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : r ≤ R)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ z₀ : Site 2, ∃ z : Int, ∃ n : Nat, let S := L.image (P.shift z₀) let Slo := S.image (P.shift (verticalShift z)) let Shi := (S.image (P.shift (verticalShift (1 + t)))).image (P.shift (verticalShift z)) (S : Set V) ⊆ E.rightHalfPlaneVertices R ∧ (Slo : Set V) ⊆ E.rightHalfPlaneVertices R ∧ 1 - 2 * Real.sqrt (1 - mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (S : Set V) (E.rightHalfPlaneBoundaryVertices r))) - 3 * epsilon < mu.real (E.finiteJoinedBoundaryArmEvent r s (s + t) n Slo Shi) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_inward_separated_finiteJoinedBoundaryArmEvent_with_margin_measureReal_gt E mu hFKG hTI hunique hrR s t L hepsilon


-- created on 2026-10-23
