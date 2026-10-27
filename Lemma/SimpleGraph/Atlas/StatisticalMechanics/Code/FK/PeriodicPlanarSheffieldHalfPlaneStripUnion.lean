import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneStripUnion
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean)
-/
@[path]
private lemma halfPlaneStripPairMergeErrorUnion_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {n : Nat}
  {L R : Finset V} :
-- imply
  MeasurableSet (E.halfPlaneStripPairMergeErrorUnion r n L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion_measurableSet E r n L R

/--
[PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean)
-/
@[path]
private lemma halfPlaneStripPairMergeErrorUnion_antitone_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {L R : Finset V} :
-- imply
  Antitone (fun n => E.halfPlaneStripPairMergeErrorUnion r n L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion_antitone E r L R

/--
[PeriodicPlaneEmbedding.halfPlanePairMergeErrorUnion_eq_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean)
-/
@[path]
private lemma halfPlanePairMergeErrorUnion_eq_product_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {L R : Finset V} :
-- imply
  E.halfPlanePairMergeErrorUnion r L R = ⋃ p : ↥(L.product R), E.halfPlanePairMergeError r p.1.1 p.1.2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.halfPlanePairMergeErrorUnion_eq_product E r L R

/--
[PeriodicPlaneEmbedding.iInter_halfPlaneStripPairMergeErrorUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean)
-/
@[path]
private lemma iInter_halfPlaneStripPairMergeErrorUnion_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {L R : Finset V} :
-- imply
  (⋂ n : Nat, E.halfPlaneStripPairMergeErrorUnion r n L R) = E.halfPlanePairMergeErrorUnion r L R := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iInter_halfPlaneStripPairMergeErrorUnion E r L R

/--
[PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion_measureReal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean)
-/
@[path]
private lemma halfPlaneStripPairMergeErrorUnion_measureReal_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
  {L R : Finset V} :
-- imply
  Tendsto (fun n => mu.real (E.halfPlaneStripPairMergeErrorUnion r n L R)) atTop (nhds (mu.real (E.halfPlanePairMergeErrorUnion r L R))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion_measureReal_tendsto E mu r L R

/--
[PeriodicPlaneEmbedding.exists_shift_stripPairMergeErrorUnion_measureReal_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean)
-/
@[path]
private lemma exists_shift_stripPairMergeErrorUnion_measureReal_lt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
  {L R : Finset V}
  {epsilon : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ z : Site 2, ∃ n : Nat, mu.real (E.halfPlaneStripPairMergeErrorUnion r n (L.image (P.shift z)) (R.image (P.shift z))) < epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_shift_stripPairMergeErrorUnion_measureReal_lt E mu hTI hunique r L R hepsilon

/--
[PeriodicPlaneEmbedding.shift_image_rightHalfPlaneStripVertices_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean)
-/
@[path]
private lemma shift_image_rightHalfPlaneStripVertices_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {t : Int}
  {r : Real}
  {n : Nat} :
-- imply
  P.shift (verticalShift t) '' E.rightHalfPlaneStripVertices r n = E.rightHalfPlaneStripVertices r n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_image_rightHalfPlaneStripVertices_vertical E t r n

/--
[PeriodicPlaneEmbedding.halfPlaneStripPairMergeError_configTranslate_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean)
-/
@[path]
private lemma halfPlaneStripPairMergeError_configTranslate_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {t : Int}
  {omega : ConfigSpace (Sym2 V)}
  {r : Real}
  {n : Nat}
  {x y : V} :
-- imply
  P.configTranslate (verticalShift t) omega ∈ E.halfPlaneStripPairMergeError r n (P.shift (verticalShift t) x) (P.shift (verticalShift t) y) ↔ omega ∈ E.halfPlaneStripPairMergeError r n x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.halfPlaneStripPairMergeError_configTranslate_vertical E t omega r n x y

/--
[PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion_configTranslate_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean)
-/
@[path]
private lemma halfPlaneStripPairMergeErrorUnion_configTranslate_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {t : Int}
  {omega : ConfigSpace (Sym2 V)}
  {r : Real}
  {n : Nat}
  {L R : Finset V} :
-- imply
  P.configTranslate (verticalShift t) omega ∈ E.halfPlaneStripPairMergeErrorUnion r n (L.image (P.shift (verticalShift t))) (R.image (P.shift (verticalShift t))) ↔ omega ∈ E.halfPlaneStripPairMergeErrorUnion r n L R := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion_configTranslate_vertical E t omega r n L R

/--
[PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion_measureReal_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean)
-/
@[path]
private lemma halfPlaneStripPairMergeErrorUnion_measureReal_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {t : Int}
  {r : Real}
  {n : Nat}
  {L R : Finset V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (E.halfPlaneStripPairMergeErrorUnion r n (L.image (P.shift (verticalShift t))) (R.image (P.shift (verticalShift t)))) = mu.real (E.halfPlaneStripPairMergeErrorUnion r n L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion_measureReal_vertical E mu hTI t r n L R

/--
[PeriodicPlaneEmbedding.exists_shift_stripPairMergeErrorUnion_measureReal_lt_with_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean)
-/
@[path]
private lemma exists_shift_stripPairMergeErrorUnion_measureReal_lt_with_sources_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
  {L R : Finset V}
  {epsilon : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ z : Site 2, ∃ n : Nat, (L.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices r ∧ (R.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices r ∧ mu.real (E.halfPlaneStripPairMergeErrorUnion r n (L.image (P.shift z)) (R.image (P.shift z))) < epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_shift_stripPairMergeErrorUnion_measureReal_lt_with_sources E mu hTI hunique r L R hepsilon

/--
[PeriodicPlaneEmbedding.exists_shift_stripPairMergeErrorUnion_measureReal_lt_with_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean)
-/
@[path]
private lemma exists_shift_stripPairMergeErrorUnion_measureReal_lt_with_margin_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R : Real}
  {L Rset : Finset V}
  {epsilon : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : r ≤ R)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ z : Site 2, ∃ n : Nat, (L.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices R ∧ (Rset.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices R ∧ mu.real (E.halfPlaneStripPairMergeErrorUnion r n (L.image (P.shift z)) (Rset.image (P.shift z))) < epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_shift_stripPairMergeErrorUnion_measureReal_lt_with_margin E mu hTI hunique hrR L Rset hepsilon

/--
[PeriodicPlaneEmbedding.exists_inward_adjacent_stripPlacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean)
-/
@[path]
private lemma exists_inward_adjacent_stripPlacement_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
  {L : Finset V}
  {epsilon : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ z : Site 2, ∃ n : Nat, (L.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices r ∧ ((L.image (P.shift z)).image (P.shift (verticalShift 1)) : Set V) ⊆ E.rightHalfPlaneVertices r ∧ mu.real (E.halfPlaneStripPairMergeErrorUnion r n (L.image (P.shift z)) ((L.image (P.shift z)).image (P.shift (verticalShift 1)))) < epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_inward_adjacent_stripPlacement E mu hTI hunique r L hepsilon

/--
[PeriodicPlaneEmbedding.exists_inward_adjacent_stripPlacement_with_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean)
-/
@[path]
private lemma exists_inward_adjacent_stripPlacement_with_margin_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R : Real}
  {L : Finset V}
  {epsilon : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : r ≤ R)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ z : Site 2, ∃ n : Nat, (L.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices R ∧ ((L.image (P.shift z)).image (P.shift (verticalShift 1)) : Set V) ⊆ E.rightHalfPlaneVertices R ∧ mu.real (E.halfPlaneStripPairMergeErrorUnion r n (L.image (P.shift z)) ((L.image (P.shift z)).image (P.shift (verticalShift 1)))) < epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_inward_adjacent_stripPlacement_with_margin E mu hTI hunique hrR L hepsilon

/--
[PeriodicPlaneEmbedding.exists_inward_twoStep_stripPlacement_with_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean)
-/
@[path]
private lemma exists_inward_twoStep_stripPlacement_with_margin_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R : Real}
  {L : Finset V}
  {epsilon : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : r ≤ R)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ z : Site 2, ∃ n : Nat, (L.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices R ∧ ((L.image (P.shift z)).image (P.shift (verticalShift 2)) : Set V) ⊆ E.rightHalfPlaneVertices R ∧ mu.real (E.halfPlaneStripPairMergeErrorUnion r n (L.image (P.shift z)) ((L.image (P.shift z)).image (P.shift (verticalShift 2)))) < epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_inward_twoStep_stripPlacement_with_margin E mu hTI hunique hrR L hepsilon

/--
[PeriodicPlaneEmbedding.exists_inward_separated_stripPlacement_with_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean)
-/
@[path]
private lemma exists_inward_separated_stripPlacement_with_margin_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R : Real}
  {t : Int}
  {L : Finset V}
  {epsilon : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : r ≤ R)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ z : Site 2, ∃ n : Nat, (L.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices R ∧ ((L.image (P.shift z)).image (P.shift (verticalShift (1 + t))) : Set V) ⊆ E.rightHalfPlaneVertices R ∧ mu.real (E.halfPlaneStripPairMergeErrorUnion r n (L.image (P.shift z)) ((L.image (P.shift z)).image (P.shift (verticalShift (1 + t))))) < epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_inward_separated_stripPlacement_with_margin E mu hTI hunique hrR t L hepsilon


-- created on 2026-10-23
