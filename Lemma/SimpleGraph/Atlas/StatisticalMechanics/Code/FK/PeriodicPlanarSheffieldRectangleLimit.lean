import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectangleLimit
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[exists_preferenceKingOffset_of_kingAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleLimit.lean)
-/
@[path]
private lemma exists_preferenceKingOffset_of_kingAdj_eq
  [DecidableEq V]
  [Countable V]
  {x y : Site 2}
-- given
  (hxy : KingAdj x y) :
-- imply
  ∃ ij : Fin 3 × Fin 3, y = x + preferenceKingOffset ij := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_preferenceKingOffset_of_kingAdj hxy

/--
[PeriodicPlaneEmbedding.crossing_branch_of_preference_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleLimit.lean)
-/
@[path]
private lemma crossing_branch_of_preference_witness_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {N : Nat}
  {a b c d : Real}
  {x xVertical xHorizontal : Site 2}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hbox : ((P.orbitBox N).image (P.shift x) : Set V) ⊆ E.rectVertices a b c d)
  (hBottomTop : mu.real (E.rectSideConnectionEvent a b c d ((P.orbitBox N).image (P.shift x) : Set V) (E.rectTopBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d ((P.orbitBox N).image (P.shift x) : Set V) (E.rectBottomBoundaryVertices a b c d)))
  (hLeftRight : mu.real (E.rectSideConnectionEvent a b c d ((P.orbitBox N).image (P.shift x) : Set V) (E.rectRightBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d ((P.orbitBox N).image (P.shift x) : Set V) (E.rectLeftBoundaryVertices a b c d)))
  (hVerticalOpposite : mu.real (E.rectSideConnectionEvent a b c d ((P.orbitBox N).image (P.shift xVertical) : Set V) (E.rectBottomBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d ((P.orbitBox N).image (P.shift xVertical) : Set V) (E.rectTopBoundaryVertices a b c d)))
  (hHorizontalOpposite : mu.real (E.rectSideConnectionEvent a b c d ((P.orbitBox N).image (P.shift xHorizontal) : Set V) (E.rectLeftBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d ((P.orbitBox N).image (P.shift xHorizontal) : Set V) (E.rectRightBoundaryVertices a b c d))) :
-- imply
  let L := (P.orbitBox N).image (P.shift x) let RV := (P.orbitBox N).image (P.shift xVertical) let RH := (P.orbitBox N).image (P.shift xHorizontal) let Ab := mu.real (E.rectSideConnectionEvent a b c d (L : Set V) (E.rectBottomBoundaryVertices a b c d)) let Al := mu.real (E.rectSideConnectionEvent a b c d (L : Set V) (E.rectLeftBoundaryVertices a b c d)) let A := max Ab Al let Hv := mu.real (P.setHitsInfinite (RV : Set V)) let Hh := mu.real (P.setHitsInfinite (RH : Set V)) let Mv := mu.real (E.rectanglePairMergeErrorUnion a b c d L RV) let Mh := mu.real (E.rectanglePairMergeErrorUnion a b c d L RH) 1 - Real.sqrt (Real.sqrt (1 - mu.real (P.orbitBoxHitsInfinite N))) ≤ A ∧ (A * (Hv * A - Mv) - Mv ≤ mu.real (E.verticalCrossingEvent a b c d) ∨ A * (Hh * A - Mh) - Mh ≤ mu.real (E.horizontalCrossingEvent a b c d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.crossing_branch_of_preference_witness E mu hFKG hTI N a b c d x xVertical xHorizontal hbox hBottomTop hLeftRight hVerticalOpposite hHorizontalOpposite

/--
[PeriodicGraph.exists_common_pairMergeRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleLimit.lean)
-/
@[path]
private lemma exists_common_pairMergeRadius_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (L R₁ R₂ : Nat -> Finset V) :
-- imply
  ∃ radius : Nat -> Nat, ∀ n, n ≤ radius n ∧ mu.real (P.pairMergeErrorUnion (L n) (R₁ n) (radius n)) < (1 : Real) / (n + 1) ∧ mu.real (P.pairMergeErrorUnion (L n) (R₂ n) (radius n)) < (1 : Real) / (n + 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_common_pairMergeRadius P mu hunique L R₁ R₂

/--
[PeriodicGraph.exists_uniform_pairMergeRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleLimit.lean)
-/
@[path]
private lemma exists_uniform_pairMergeRadius_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  [Fintype ι]
  [DecidableEq ι]
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (L : Nat -> Finset V)
  (R : Nat -> ι -> Finset V) :
-- imply
  ∃ radius : Nat -> Nat, ∀ n, n ≤ radius n ∧ ∀ i, mu.real (P.pairMergeErrorUnion (L n) (R n i) (radius n)) < (1 : Real) / (n + 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_uniform_pairMergeRadius P mu hunique L R

/--
[PeriodicPlaneEmbedding.exists_translated_pairMergeErrors_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleLimit.lean)
-/
@[path]
private lemma exists_translated_pairMergeErrors_tendsto_zero_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (z : Nat -> Site 2)
  (L R₁ R₂ : Nat -> Finset V) :
-- imply
  ∃ radius : Nat -> Nat, (∀ n, n ≤ radius n) ∧ ∀ (a b c d : Nat -> Real), (∀ n, (P.shift (z n) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) -> Tendsto (fun n => mu.real (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n) ((L n).image (P.shift (z n))) ((R₁ n).image (P.shift (z n))))) atTop (nhds 0) ∧ Tendsto (fun n => mu.real (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n) ((L n).image (P.shift (z n))) ((R₂ n).image (P.shift (z n))))) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_translated_pairMergeErrors_tendsto_zero E mu hTI hunique z L R₁ R₂

/--
[PeriodicPlaneEmbedding.exists_uniform_kingOffset_mergeError_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleLimit.lean)
-/
@[path]
private lemma exists_uniform_kingOffset_mergeError_tendsto_zero_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  ∃ radius : Nat -> Nat, (∀ n, n ≤ radius n) ∧ ∀ (x : Nat -> Site 2) (ij : Nat -> Fin 3 × Fin 3) (a b c d : Nat -> Real), (∀ n, (P.shift (x n) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) -> Tendsto (fun n => mu.real (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (x n))) ((P.orbitBox n).image (P.shift (x n + preferenceKingOffset (ij n)))))) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniform_kingOffset_mergeError_tendsto_zero E mu hTI hunique

/--
[PeriodicPlaneEmbedding.exists_connectorRadius_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleLimit.lean)
-/
@[path]
private lemma exists_connectorRadius_crossing_max_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (x xVertical xHorizontal : Nat -> Site 2) :
-- imply
  ∃ radius : Nat -> Nat, ∀ (a b c d : Nat -> Real), (∀ n, (P.shift (x n) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) -> (∀ n, mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (x n)) : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))) ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (x n)) : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) -> (∀ n, mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (x n)) : Set V) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n))) ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (x n)) : Set V) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) -> (∀ n, mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (xVertical n)) : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))) ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (xVertical n)) : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) -> (∀ n, mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (xHorizontal n)) : Set V) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n))) ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (xHorizontal n)) : Set V) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) -> Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))) (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_connectorRadius_crossing_max_tendsto_one E mu hFKG hTI hunique x xVertical xHorizontal

/--
[PeriodicPlaneEmbedding.exists_uniform_connectorRadius_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleLimit.lean)
-/
@[path]
private lemma exists_uniform_connectorRadius_crossing_max_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  ∃ radius : Nat -> Nat, ∀ (x : Nat -> Site 2) (ijVertical ijHorizontal : Nat -> Fin 3 × Fin 3) (a b c d : Nat -> Real), (∀ n, (P.shift (x n) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) -> (∀ n, mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (x n)) : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))) ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (x n)) : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) -> (∀ n, mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (x n)) : Set V) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n))) ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (x n)) : Set V) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) -> (∀ n, mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (x n + preferenceKingOffset (ijVertical n))) : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))) ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (x n + preferenceKingOffset (ijVertical n))) : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) -> (∀ n, mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (x n + preferenceKingOffset (ijHorizontal n))) : Set V) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n))) ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((P.orbitBox n).image (P.shift (x n + preferenceKingOffset (ijHorizontal n))) : Set V) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) -> Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))) (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniform_connectorRadius_crossing_max_tendsto_one E mu hFKG hTI hunique


-- created on 2026-10-23
