import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDualTranslated
open MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[PeriodicGraph.translatedFiniteInfinitePairConnectionEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTranslated.lean)
-/
@[path]
private lemma translatedFiniteInfinitePairConnectionEvent_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {L R : Finset V}
  {N : Nat} :
-- imply
  MeasurableSet (P.translatedFiniteInfinitePairConnectionEvent z L R N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.translatedFiniteInfinitePairConnectionEvent_measurableSet P z L R N

/--
[PeriodicGraph.translatedFiniteInfinitePairConnectionEvent_measureReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTranslated.lean)
-/
@[path]
private lemma translatedFiniteInfinitePairConnectionEvent_measureReal_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {z : Site 2}
  {L R : Finset V}
  {N : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (P.translatedFiniteInfinitePairConnectionEvent z L R N) = mu.real (P.finiteInfinitePairConnectionEvent L R N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.translatedFiniteInfinitePairConnectionEvent_measureReal P mu hTI z L R N

/--
[PeriodicGraph.shiftGraphHom_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTranslated.lean)
-/
@[path]
private lemma shiftGraphHom_apply_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {v : V} :
-- imply
  P.shiftGraphHom z v = P.shift z v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.shiftGraphHom_apply P z v

/--
[PeriodicGraph.translatedFiniteInfinitePairConnectionEvent_graphWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTranslated.lean)
-/
@[path]
private lemma translatedFiniteInfinitePairConnectionEvent_graphWalk_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {z : Site 2}
  {L R : Finset V}
  {N : Nat}
-- given
  (h : omega ∈ P.translatedFiniteInfinitePairConnectionEvent z L R N) :
-- imply
  ∃ x ∈ L.image (P.shift (-z)), ∃ y ∈ R.image (P.shift (-z)), ∃ q : P.graph.Walk x y, (∀ v ∈ q.support, v ∈ (P.orbitBox (P.bufferedRadius N)).image (P.shift (-z))) ∧ ∀ {u v : V}, s(u, v) ∈ q.edges → omega s(u, v) = true := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.translatedFiniteInfinitePairConnectionEvent_graphWalk P h

/--
[PeriodicGraph.exists_uniformRadius_highProbability_translatedFiniteEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTranslated.lean)
-/
@[path]
private lemma exists_uniformRadius_highProbability_translatedFiniteEvent_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {epsilon : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ n : Nat, ∀ zL zR : Site 2, ∃ N : Nat, ∀ z : Site 2, 1 - epsilon < mu.real (P.translatedFiniteInfinitePairConnectionEvent z ((P.orbitBox n).image (P.shift zL)) ((P.orbitBox n).image (P.shift zR)) N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_uniformRadius_highProbability_translatedFiniteEvent P mu hTI hunique hepsilon

/--
[PeriodicPlanarDualPair.dualMeasure_measureReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTranslated.lean)
-/
@[path]
private lemma dualMeasure_measureReal_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {Pdual : PeriodicGraph W}
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {A : Set (ConfigSpace (Sym2 W))}
-- given
  (hA : MeasurableSet A) :
-- imply
  (D.dualMeasure mu).real A = mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' A) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualMeasure_measureReal D mu hA

/--
[PeriodicPlanarDualPair.exists_uniformRadius_highProbability_complementaryDualFiniteEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTranslated.lean)
-/
@[path]
private lemma exists_uniformRadius_highProbability_complementaryDualFiniteEvent_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {Pdual : PeriodicGraph W}
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {epsilon : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hdualUnique : D.dualMeasure mu {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ n : Nat, ∀ zL zR : Site 2, ∃ N : Nat, ∀ z : Site 2, 1 - epsilon < mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' Pdual.translatedFiniteInfinitePairConnectionEvent z ((Pdual.orbitBox n).image (Pdual.shift zL)) ((Pdual.orbitBox n).image (Pdual.shift zR)) N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_uniformRadius_highProbability_complementaryDualFiniteEvent D mu hTI hdualUnique hepsilon

/--
[PeriodicPlaneEmbedding.exists_verticalGap_shift_orbitBox_middleThird](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTranslated.lean)
-/
@[path]
private lemma exists_verticalGap_shift_orbitBox_middleThird_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {N : Nat}
  {B s : Real} :
-- imply
  ∃ gap : Int, 0 < (gap : Real) ∧ ∃ z : Site 2, z 0 = 0 ∧ ∀ v ∈ (P.orbitBox (P.bufferedRadius N)).image (P.shift (-z)), (2 * s + (s + gap)) / 3 + B < E.vertexCoord v 1 ∧ E.vertexCoord v 1 < (s + 2 * (s + gap)) / 3 - B := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_verticalGap_shift_orbitBox_middleThird E N B s

/--
[exists_verticalGap_translatedDualPlacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTranslated.lean)
-/
@[path]
private lemma exists_verticalGap_translatedDualPlacement_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {N : Nat}
  {Bd s a b : Real}
  {Ld Rd : Finset W}
-- given
  (hLd : ∀ y ∈ Ld, D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0 < a)
  (hRd : ∀ y ∈ Rd, b < D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0) :
-- imply
  ∃ gap : Int, 0 < (gap : Real) ∧ ∃ z : Site 2, (∀ y ∈ Ld.image (Pdual.shift (-z)), D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0 < a) ∧ (∀ y ∈ Rd.image (Pdual.shift (-z)), b < D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0) ∧ ∀ v ∈ (Pdual.orbitBox (Pdual.bufferedRadius N)).image (Pdual.shift (-z)), (2 * s + (s + gap)) / 3 + Bd < D.dualEmbedding.vertexCoord v 1 ∧ D.dualEmbedding.vertexCoord v 1 < (s + 2 * (s + gap)) / 3 - Bd := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_verticalGap_translatedDualPlacement D N Bd s a b hLd hRd

/--
[translatedFiniteStripPrimal_dualPairConnection_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTranslated.lean)
-/
@[path]
private lemma translatedFiniteStripPrimal_dualPairConnection_disjoint_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {omega : ConfigSpace (Sym2 V)}
  {z : Site 2}
  {Bp Bd r s : Real}
  {gap : Int}
  {np N : Nat}
  {Lp Rp : Finset V}
  {Ld Rd : Finset W}
-- given
  (hBp0 : 0 ≤ Bp)
  (hBd0 : 0 ≤ Bd)
  (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ Bp)
  (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ Bd)
  (hgap : 0 < (gap : Real))
  (hLpDeep : (Lp : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices (r + Bp))
  (hLd : ∀ y ∈ Ld.image (Pdual.shift (-z)), D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0 < r - Bp - 1)
  (hRd : ∀ y ∈ Rd.image (Pdual.shift (-z)), r + np + Bp + 1 < D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0)
  (hbox : ∀ v ∈ (Pdual.orbitBox (Pdual.bufferedRadius N)).image (Pdual.shift (-z)), (2 * s + (s + gap)) / 3 + Bd < D.dualEmbedding.vertexCoord v 1 ∧ D.dualEmbedding.vertexCoord v 1 < (s + 2 * (s + gap)) / 3 - Bd)
  (hprimal : omega ∈ D.primalEmbedding.finiteStripJoinedBoundaryArmEvent r s (s + gap) np Lp Rp)
  (hdual : dualConfigEquiv D.edgeDual omega ∈ Pdual.translatedFiniteInfinitePairConnectionEvent z Ld Rd N) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.translatedFiniteStripPrimal_dualPairConnection_disjoint D omega hBp0 hBd0 hBp hBd hgap hLpDeep hLd hRd hbox hprimal hdual

/--
[exists_verticalGap_translatedFiniteStripPrimal_dualPairConnection_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTranslated.lean)
-/
@[path]
private lemma exists_verticalGap_translatedFiniteStripPrimal_dualPairConnection_disjoint_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {Bp Bd r s : Real}
  {np N : Nat}
  {Lp Rp : Finset V}
  {Ld Rd : Finset W}
-- given
  (hBp0 : 0 ≤ Bp)
  (hBd0 : 0 ≤ Bd)
  (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ Bp)
  (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ Bd)
  (hLpDeep : (Lp : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices (r + Bp))
  (hLd : ∀ y ∈ Ld, D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0 < r - Bp - 1)
  (hRd : ∀ y ∈ Rd, r + np + Bp + 1 < D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0) :
-- imply
  ∃ gap : Int, ∃ z : Site 2, 0 < (gap : Real) ∧ ∀ omega : ConfigSpace (Sym2 V), omega ∈ D.primalEmbedding.finiteStripJoinedBoundaryArmEvent r s (s + gap) np Lp Rp → dualConfigEquiv D.edgeDual omega ∈ Pdual.translatedFiniteInfinitePairConnectionEvent z Ld Rd N → False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_verticalGap_translatedFiniteStripPrimal_dualPairConnection_disjoint D hBp0 hBd0 hBp hBd hLpDeep hLd hRd

/--
[exists_verticalGap_translatedFiniteEvents_measureReal_add_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTranslated.lean)
-/
@[path]
private lemma exists_verticalGap_translatedFiniteEvents_measureReal_add_le_one_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {Bp Bd r s : Real}
  {np N : Nat}
  {Lp Rp : Finset V}
  {Ld Rd : Finset W}
-- given
  (hBp0 : 0 ≤ Bp)
  (hBd0 : 0 ≤ Bd)
  (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ Bp)
  (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ Bd)
  (hLpDeep : (Lp : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices (r + Bp))
  (hLd : ∀ y ∈ Ld, D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0 < r - Bp - 1)
  (hRd : ∀ y ∈ Rd, r + np + Bp + 1 < D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0) :
-- imply
  ∃ gap : Int, ∃ z : Site 2, 0 < (gap : Real) ∧ mu.real (D.primalEmbedding.finiteStripJoinedBoundaryArmEvent r s (s + gap) np Lp Rp) + mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' Pdual.translatedFiniteInfinitePairConnectionEvent z Ld Rd N) ≤ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_verticalGap_translatedFiniteEvents_measureReal_add_le_one D mu hBp0 hBd0 hBp hBd hLpDeep hLd hRd

/--
[exists_verticalGap_not_both_translatedFiniteEvents_highProbability](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTranslated.lean)
-/
@[path]
private lemma exists_verticalGap_not_both_translatedFiniteEvents_highProbability_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {Bp Bd r s epsilon : Real}
  {np N : Nat}
  {Lp Rp : Finset V}
  {Ld Rd : Finset W}
-- given
  (hepsilon : epsilon < 1 / 2)
  (hBp0 : 0 ≤ Bp)
  (hBd0 : 0 ≤ Bd)
  (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ Bp)
  (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ Bd)
  (hLpDeep : (Lp : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices (r + Bp))
  (hLd : ∀ y ∈ Ld, D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0 < r - Bp - 1)
  (hRd : ∀ y ∈ Rd, r + np + Bp + 1 < D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0) :
-- imply
  ∃ gap : Int, ∃ z : Site 2, 0 < (gap : Real) ∧ ¬(1 - epsilon < mu.real (D.primalEmbedding.finiteStripJoinedBoundaryArmEvent r s (s + gap) np Lp Rp) ∧ 1 - epsilon < mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' Pdual.translatedFiniteInfinitePairConnectionEvent z Ld Rd N)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_verticalGap_not_both_translatedFiniteEvents_highProbability D mu hepsilon hBp0 hBd0 hBp hBd hLpDeep hLd hRd


-- created on 2026-10-23
