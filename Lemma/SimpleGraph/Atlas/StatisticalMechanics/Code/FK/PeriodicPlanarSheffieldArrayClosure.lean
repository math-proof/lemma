import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure.Part12
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[horizontalShift_zero_vector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma horizontalShift_zero_vector_eq
  [DecidableEq V]
  [Countable V] :
-- imply
  horizontalShift 0 = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.horizontalShift_zero_vector

/--
[verticalShift_zero_vector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma verticalShift_zero_vector_eq
  [DecidableEq V]
  [Countable V] :
-- imply
  verticalShift 0 = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.verticalShift_zero_vector

/--
[PeriodicPlaneEmbedding.rectSideConnectionEvent_union_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma rectSideConnectionEvent_union_source_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {S T side : Set V} :
-- imply
  E.rectSideConnectionEvent a b c d (S ∪ T) side = E.rectSideConnectionEvent a b c d S side ∪ E.rectSideConnectionEvent a b c d T side := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectSideConnectionEvent_union_source E a b c d S T side

/--
[PeriodicGraph.fourShiftTemplate_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma fourShiftTemplate_add_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {S : Finset V}
  {zLeft zRight zBottom zTop t : Site 2} :
-- imply
  P.fourShiftTemplate S (zLeft + t) (zRight + t) (zBottom + t) (zTop + t) = (P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift t) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.fourShiftTemplate_add P S zLeft zRight zBottom zTop t

/--
[PeriodicGraph.fourShiftTemplate_add_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma fourShiftTemplate_add_image_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {S : Finset V}
  {zLeft zRight zBottom zTop t w : Site 2} :
-- imply
  (P.fourShiftTemplate S (zLeft + t) (zRight + t) (zBottom + t) (zTop + t)).image (P.shift w) = (P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift (t + w)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.fourShiftTemplate_add_image P S zLeft zRight zBottom zTop t w

/--
[PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_mono_rectangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma rectanglePairMergeErrorUnion_mono_rectangle_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d a' b' c' d' : Real}
  {L R : Finset V}
-- given
  (ha : a' ≤ a)
  (hb : b ≤ b')
  (hc : c' ≤ c)
  (hd : d ≤ d') :
-- imply
  E.rectanglePairMergeErrorUnion a' b' c' d' L R ⊆ E.rectanglePairMergeErrorUnion a b c d L R := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_mono_rectangle E L R ha hb hc hd

/--
[PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_mono_rectangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma rectanglePairMergeErrorUnion_measureReal_mono_rectangle_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {a b c d a' b' c' d' : Real}
  {L R : Finset V}
-- given
  (ha : a' ≤ a)
  (hb : b ≤ b')
  (hc : c' ≤ c)
  (hd : d ≤ d') :
-- imply
  mu.real (E.rectanglePairMergeErrorUnion a' b' c' d' L R) ≤ mu.real (E.rectanglePairMergeErrorUnion a b c d L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_mono_rectangle E mu L R ha hb hc hd

/--
[PeriodicPlaneEmbedding.rectBottomConnection_component_le_template_of_enlarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma rectBottomConnection_component_le_template_of_enlarge_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {a b c d a' b' d' : Real}
  {component template : Finset V}
-- given
  (hcomponent : component ⊆ template)
  (ha : a' ≤ a)
  (hb : b ≤ b')
  (hd : d ≤ d') :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d (component : Set V) (E.rectBottomBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a' b' c d' (template : Set V) (E.rectBottomBoundaryVertices a' b' c d')) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectBottomConnection_component_le_template_of_enlarge E mu component template hcomponent ha hb hd

/--
[PeriodicPlaneEmbedding.rectTopConnection_component_le_template_of_enlarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma rectTopConnection_component_le_template_of_enlarge_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {a b c d a' b' c' : Real}
  {component template : Finset V}
-- given
  (hcomponent : component ⊆ template)
  (ha : a' ≤ a)
  (hb : b ≤ b')
  (hc : c' ≤ c) :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d (component : Set V) (E.rectTopBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a' b' c' d (template : Set V) (E.rectTopBoundaryVertices a' b' c' d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectTopConnection_component_le_template_of_enlarge E mu component template hcomponent ha hb hc

/--
[PeriodicPlaneEmbedding.rectLeftConnection_component_le_template_of_enlarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma rectLeftConnection_component_le_template_of_enlarge_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {a b c d b' c' d' : Real}
  {component template : Finset V}
-- given
  (hcomponent : component ⊆ template)
  (hb : b ≤ b')
  (hc : c' ≤ c)
  (hd : d ≤ d') :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d (component : Set V) (E.rectLeftBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b' c' d' (template : Set V) (E.rectLeftBoundaryVertices a b' c' d')) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectLeftConnection_component_le_template_of_enlarge E mu component template hcomponent hb hc hd

/--
[PeriodicPlaneEmbedding.rectRightConnection_component_le_template_of_enlarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma rectRightConnection_component_le_template_of_enlarge_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {a b c d a' c' d' : Real}
  {component template : Finset V}
-- given
  (hcomponent : component ⊆ template)
  (ha : a' ≤ a)
  (hc : c' ≤ c)
  (hd : d ≤ d') :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d (component : Set V) (E.rectRightBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a' b c' d' (template : Set V) (E.rectRightBoundaryVertices a' b c' d')) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectRightConnection_component_le_template_of_enlarge E mu component template hcomponent ha hc hd

/--
[PeriodicPlaneEmbedding.verticalCrossing_ge_carriedComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma verticalCrossing_ge_carriedComponents_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {L R : Finset V}
  {aBottom bBottom dBottom aTop bTop cTop : Real}
  {aMerge bMerge cMerge dMerge : Real}
-- given
  (hFKG : IsFKG mu)
  (hBottomA : a ≤ aBottom)
  (hBottomB : bBottom ≤ b)
  (hBottomD : dBottom ≤ d)
  (hTopA : a ≤ aTop)
  (hTopB : bTop ≤ b)
  (hTopC : c ≤ cTop)
  (hMergeA : a ≤ aMerge)
  (hMergeB : bMerge ≤ b)
  (hMergeC : c ≤ cMerge)
  (hMergeD : dMerge ≤ d) :
-- imply
  mu.real (E.rectSideConnectionEvent aBottom bBottom c dBottom (L : Set V) (E.rectBottomBoundaryVertices aBottom bBottom c dBottom)) * mu.real (E.rectSideConnectionEvent aTop bTop cTop d (R : Set V) (E.rectTopBoundaryVertices aTop bTop cTop d)) - mu.real (E.rectanglePairMergeErrorUnion aMerge bMerge cMerge dMerge L R) ≤ mu.real (E.verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossing_ge_carriedComponents E mu hFKG a b c d L R aBottom bBottom dBottom aTop bTop cTop aMerge bMerge cMerge dMerge hBottomA hBottomB hBottomD hTopA hTopB hTopC hMergeA hMergeB hMergeC hMergeD

/--
[PeriodicPlaneEmbedding.horizontalCrossing_ge_carriedComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma horizontalCrossing_ge_carriedComponents_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {L R : Finset V}
  {bLeft cLeft dLeft aRight cRight dRight : Real}
  {aMerge bMerge cMerge dMerge : Real}
-- given
  (hFKG : IsFKG mu)
  (hLeftB : bLeft ≤ b)
  (hLeftC : c ≤ cLeft)
  (hLeftD : dLeft ≤ d)
  (hRightA : a ≤ aRight)
  (hRightC : c ≤ cRight)
  (hRightD : dRight ≤ d)
  (hMergeA : a ≤ aMerge)
  (hMergeB : bMerge ≤ b)
  (hMergeC : c ≤ cMerge)
  (hMergeD : dMerge ≤ d) :
-- imply
  mu.real (E.rectSideConnectionEvent a bLeft cLeft dLeft (L : Set V) (E.rectLeftBoundaryVertices a bLeft cLeft dLeft)) * mu.real (E.rectSideConnectionEvent aRight b cRight dRight (R : Set V) (E.rectRightBoundaryVertices aRight b cRight dRight)) - mu.real (E.rectanglePairMergeErrorUnion aMerge bMerge cMerge dMerge L R) ≤ mu.real (E.horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossing_ge_carriedComponents E mu hFKG a b c d L R bLeft cLeft dLeft aRight cRight dRight aMerge bMerge cMerge dMerge hLeftB hLeftC hLeftD hRightA hRightC hRightD hMergeA hMergeB hMergeC hMergeD

/--
[PeriodicPlaneEmbedding.verticalCrossing_ge_carriedComponents_of_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma verticalCrossing_ge_carriedComponents_of_connector_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d a' b' : Real}
  {bottom top : Finset V}
  {radius : Nat}
-- given
  (hFKG : IsFKG mu)
  (ha : a' ≤ a)
  (hb : b ≤ b')
  (hbox : (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆ E.rectVertices a' b' c d) :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d (bottom : Set V) (E.rectBottomBoundaryVertices a b c d)) * mu.real (E.rectSideConnectionEvent a b c d (top : Set V) (E.rectTopBoundaryVertices a b c d)) - mu.real (P.pairMergeErrorUnion bottom top radius) ≤ mu.real (E.verticalCrossingEvent a' b' c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossing_ge_carriedComponents_of_connector E mu hFKG a b c d a' b' bottom top radius ha hb hbox

/--
[PeriodicPlaneEmbedding.horizontalCrossing_ge_carriedComponents_of_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma horizontalCrossing_ge_carriedComponents_of_connector_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d c' d' : Real}
  {left right : Finset V}
  {radius : Nat}
-- given
  (hFKG : IsFKG mu)
  (hc : c' ≤ c)
  (hd : d ≤ d')
  (hbox : (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆ E.rectVertices a b c' d') :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d (left : Set V) (E.rectLeftBoundaryVertices a b c d)) * mu.real (E.rectSideConnectionEvent a b c d (right : Set V) (E.rectRightBoundaryVertices a b c d)) - mu.real (P.pairMergeErrorUnion left right radius) ≤ mu.real (E.horizontalCrossingEvent a b c' d') := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossing_ge_carriedComponents_of_connector E mu hFKG a b c d c' d' left right radius hc hd hbox

/--
[PeriodicPlaneEmbedding.verticalCrossing_tendsto_one_of_carriedComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma verticalCrossing_tendsto_one_of_carriedComponents_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d a' b' : Nat → Real}
  {bottom top : Nat → Finset V}
  {radius : Nat → Nat}
-- given
  (hFKG : IsFKG mu)
  (ha : ∀ n, a' n ≤ a n)
  (hb : ∀ n, b n ≤ b' n)
  (hbox : ∀ n, (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆ E.rectVertices (a' n) (b' n) (c n) (d n))
  (hbottom : Tendsto (fun n ↦ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (bottom n : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) atTop (nhds 1))
  (htop : Tendsto (fun n ↦ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (top n : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) atTop (nhds 1))
  (hmerge : Tendsto (fun n ↦ mu.real (P.pairMergeErrorUnion (bottom n) (top n) (radius n))) atTop (nhds 0)) :
-- imply
  Tendsto (fun n ↦ mu.real (E.verticalCrossingEvent (a' n) (b' n) (c n) (d n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossing_tendsto_one_of_carriedComponents E mu hFKG a b c d a' b' bottom top radius ha hb hbox hbottom htop hmerge

/--
[PeriodicPlaneEmbedding.horizontalCrossing_tendsto_one_of_carriedComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma horizontalCrossing_tendsto_one_of_carriedComponents_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d c' d' : Nat → Real}
  {left right : Nat → Finset V}
  {radius : Nat → Nat}
-- given
  (hFKG : IsFKG mu)
  (hc : ∀ n, c' n ≤ c n)
  (hd : ∀ n, d n ≤ d' n)
  (hbox : ∀ n, (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆ E.rectVertices (a n) (b n) (c' n) (d' n))
  (hleft : Tendsto (fun n ↦ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (left n : Set V) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) atTop (nhds 1))
  (hright : Tendsto (fun n ↦ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (right n : Set V) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) atTop (nhds 1))
  (hmerge : Tendsto (fun n ↦ mu.real (P.pairMergeErrorUnion (left n) (right n) (radius n))) atTop (nhds 0)) :
-- imply
  Tendsto (fun n ↦ mu.real (E.horizontalCrossingEvent (a n) (b n) (c' n) (d' n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossing_tendsto_one_of_carriedComponents E mu hFKG a b c d c' d' left right radius hc hd hbox hleft hright hmerge

/--
[PeriodicPlaneEmbedding.CarriedCrossNestedArray.verticalCrossingLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma verticalCrossingLimit_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {data : E.CarriedCrossNestedArray mu}
-- given
  (hFKG : IsFKG mu) :
-- imply
  Tendsto (fun n ↦ mu.real (E.verticalCrossingEvent (data.aWide n) (data.bWide n) (data.c n) (data.d n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.CarriedCrossNestedArray.verticalCrossingLimit E mu hFKG data

/--
[PeriodicPlaneEmbedding.CarriedCrossNestedArray.horizontalCrossingLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma horizontalCrossingLimit_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {data : E.CarriedCrossNestedArray mu}
-- given
  (hFKG : IsFKG mu) :
-- imply
  Tendsto (fun n ↦ mu.real (E.horizontalCrossingEvent (data.a n) (data.b n) (data.cTall n) (data.dTall n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.CarriedCrossNestedArray.horizontalCrossingLimit E mu hFKG data

/--
[PeriodicPlaneEmbedding.CarriedCrossNestedArray.crossingMaxLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma crossingMaxLimit_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {data : E.CarriedCrossNestedArray mu}
-- given
  (hFKG : IsFKG mu) :
-- imply
  Tendsto (fun n ↦ max (mu.real (E.horizontalCrossingEvent (data.a n) (data.b n) (data.cTall n) (data.dTall n))) (mu.real (E.verticalCrossingEvent (data.aWide n) (data.bWide n) (data.c n) (data.d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.CarriedCrossNestedArray.crossingMaxLimit E mu hFKG data

/--
[PeriodicGraph.bottom_subset_fourBoundaryComponentTemplate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma bottom_subset_fourBoundaryComponentTemplate_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {bottom top left right : Finset V} :
-- imply
  bottom ⊆ P.fourBoundaryComponentTemplate bottom top left right := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bottom_subset_fourBoundaryComponentTemplate P bottom top left right

/--
[PeriodicGraph.top_subset_fourBoundaryComponentTemplate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma top_subset_fourBoundaryComponentTemplate_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {bottom top left right : Finset V} :
-- imply
  top ⊆ P.fourBoundaryComponentTemplate bottom top left right := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.top_subset_fourBoundaryComponentTemplate P bottom top left right

/--
[PeriodicGraph.left_subset_fourBoundaryComponentTemplate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma left_subset_fourBoundaryComponentTemplate_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {bottom top left right : Finset V} :
-- imply
  left ⊆ P.fourBoundaryComponentTemplate bottom top left right := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.left_subset_fourBoundaryComponentTemplate P bottom top left right

/--
[PeriodicGraph.right_subset_fourBoundaryComponentTemplate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma right_subset_fourBoundaryComponentTemplate_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {bottom top left right : Finset V} :
-- imply
  right ⊆ P.fourBoundaryComponentTemplate bottom top left right := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.right_subset_fourBoundaryComponentTemplate P bottom top left right

/--
[PeriodicPlaneEmbedding.exists_sharedBoundaryComponentTemplate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_sharedBoundaryComponentTemplate_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {p a b c d : Real}
  {bottom top left right : Finset V}
  {aBottom bBottom dBottom aTop bTop cTop : Real}
  {bLeft cLeft dLeft aRight cRight dRight : Real}
-- given
  (hBottomSource : (bottom : Set V) ⊆ E.rectVertices aBottom bBottom c dBottom)
  (hTopSource : (top : Set V) ⊆ E.rectVertices aTop bTop cTop d)
  (hLeftSource : (left : Set V) ⊆ E.rectVertices a bLeft cLeft dLeft)
  (hRightSource : (right : Set V) ⊆ E.rectVertices aRight b cRight dRight)
  (hBottomScore : p < mu.real (E.rectSideConnectionEvent aBottom bBottom c dBottom (bottom : Set V) (E.rectBottomBoundaryVertices aBottom bBottom c dBottom)))
  (hTopScore : p < mu.real (E.rectSideConnectionEvent aTop bTop cTop d (top : Set V) (E.rectTopBoundaryVertices aTop bTop cTop d)))
  (hLeftScore : p < mu.real (E.rectSideConnectionEvent a bLeft cLeft dLeft (left : Set V) (E.rectLeftBoundaryVertices a bLeft cLeft dLeft)))
  (hRightScore : p < mu.real (E.rectSideConnectionEvent aRight b cRight dRight (right : Set V) (E.rectRightBoundaryVertices aRight b cRight dRight)))
  (hBottomA : a ≤ aBottom)
  (hBottomB : bBottom ≤ b)
  (hBottomD : dBottom ≤ d)
  (hTopA : a ≤ aTop)
  (hTopB : bTop ≤ b)
  (hTopC : c ≤ cTop)
  (hLeftB : bLeft ≤ b)
  (hLeftC : c ≤ cLeft)
  (hLeftD : dLeft ≤ d)
  (hRightA : a ≤ aRight)
  (hRightC : c ≤ cRight)
  (hRightD : dRight ≤ d) :
-- imply
  let template := P.fourBoundaryComponentTemplate bottom top left right (template : Set V) ⊆ E.rectVertices a b c d ∧ p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V) (E.rectBottomBoundaryVertices a b c d)) ∧ p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V) (E.rectTopBoundaryVertices a b c d)) ∧ p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V) (E.rectLeftBoundaryVertices a b c d)) ∧ p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V) (E.rectRightBoundaryVertices a b c d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_sharedBoundaryComponentTemplate E mu p a b c d bottom top left right aBottom bBottom dBottom aTop bTop cTop bLeft cLeft dLeft aRight cRight dRight hBottomSource hTopSource hLeftSource hRightSource hBottomScore hTopScore hLeftScore hRightScore hBottomA hBottomB hBottomD hTopA hTopB hTopC hLeftB hLeftC hLeftD hRightA hRightC hRightD

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_endpointSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_endpointSources_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {p : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {a0 b0 c0 d0 a1 b1 c1 d1 : Int}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (verticalMargin horizontalMargin : Nat)
  (hbottomWidth : 2 * (family.radiusBottom verticalMargin : Int) ≤ b0 - a0)
  (htopWidth : 2 * (family.radiusTop verticalMargin : Int) ≤ b0 - a0)
  (hbottomHeight : (family.radiusBottom verticalMargin : Int) ≤ d0 - c0)
  (htopHeight : (family.radiusTop verticalMargin : Int) ≤ d0 - c0)
  (hleftWidth : (family.radiusLeft horizontalMargin : Int) ≤ b1 - a1)
  (hrightWidth : (family.radiusRight horizontalMargin : Int) ≤ b1 - a1)
  (hleftHeight : 2 * (family.radiusLeft horizontalMargin : Int) ≤ d1 - c1)
  (hrightHeight : 2 * (family.radiusRight horizontalMargin : Int) ≤ d1 - c1) :
-- imply
  ∃ bottomSource topSource leftSource rightSource : Finset V, (bottomSource : Set V) ⊆ E.rectVertices a0 b0 c0 d0 ∧ p < mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 (bottomSource : Set V) (E.rectBottomBoundaryVertices a0 b0 c0 d0)) ∧ (topSource : Set V) ⊆ E.rectVertices a0 b0 c0 d0 ∧ p < mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 (topSource : Set V) (E.rectTopBoundaryVertices a0 b0 c0 d0)) ∧ (leftSource : Set V) ⊆ E.rectVertices a1 b1 c1 d1 ∧ p < mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 (leftSource : Set V) (E.rectLeftBoundaryVertices a1 b1 c1 d1)) ∧ (rightSource : Set V) ⊆ E.rectVertices a1 b1 c1 d1 ∧ p < mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 (rightSource : Set V) (E.rectRightBoundaryVertices a1 b1 c1 d1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_endpointSources E mu hTI family verticalMargin horizontalMargin a0 b0 c0 d0 a1 b1 c1 d1 hbottomWidth htopWidth hbottomHeight htopHeight hleftWidth hrightWidth hleftHeight hrightHeight

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_sharedEndpointTemplate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_sharedEndpointTemplate_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {p : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {a b c d : Int}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (verticalMargin horizontalMargin : Nat)
  (hbottomWidth : 2 * (family.radiusBottom verticalMargin : Int) ≤ b - a)
  (htopWidth : 2 * (family.radiusTop verticalMargin : Int) ≤ b - a)
  (hbottomHeight : (family.radiusBottom verticalMargin : Int) ≤ d - c)
  (htopHeight : (family.radiusTop verticalMargin : Int) ≤ d - c)
  (hleftWidth : (family.radiusLeft horizontalMargin : Int) ≤ b - a)
  (hrightWidth : (family.radiusRight horizontalMargin : Int) ≤ b - a)
  (hleftHeight : 2 * (family.radiusLeft horizontalMargin : Int) ≤ d - c)
  (hrightHeight : 2 * (family.radiusRight horizontalMargin : Int) ≤ d - c) :
-- imply
  ∃ bottom top left right : Finset V, let template := P.fourBoundaryComponentTemplate bottom top left right (template : Set V) ⊆ E.rectVertices a b c d ∧ p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V) (E.rectBottomBoundaryVertices a b c d)) ∧ p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V) (E.rectTopBoundaryVertices a b c d)) ∧ p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V) (E.rectLeftBoundaryVertices a b c d)) ∧ p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V) (E.rectRightBoundaryVertices a b c d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_sharedEndpointTemplate E mu hTI family verticalMargin horizontalMargin a b c d hbottomWidth htopWidth hbottomHeight htopHeight hleftWidth hrightWidth hleftHeight hrightHeight

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_sharedEndpointComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_sharedEndpointComponents_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {p : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {a b c d : Int}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (verticalMargin horizontalMargin : Nat)
  (hbottomWidth : 2 * (family.radiusBottom verticalMargin : Int) ≤ b - a)
  (htopWidth : 2 * (family.radiusTop verticalMargin : Int) ≤ b - a)
  (hbottomHeight : (family.radiusBottom verticalMargin : Int) ≤ d - c)
  (htopHeight : (family.radiusTop verticalMargin : Int) ≤ d - c)
  (hleftWidth : (family.radiusLeft horizontalMargin : Int) ≤ b - a)
  (hrightWidth : (family.radiusRight horizontalMargin : Int) ≤ b - a)
  (hleftHeight : 2 * (family.radiusLeft horizontalMargin : Int) ≤ d - c)
  (hrightHeight : 2 * (family.radiusRight horizontalMargin : Int) ≤ d - c) :
-- imply
  ∃ bottom top left right : Finset V, (bottom : Set V) ⊆ E.rectVertices a b c d ∧ p < mu.real (E.rectSideConnectionEvent a b c d (bottom : Set V) (E.rectBottomBoundaryVertices a b c d)) ∧ (top : Set V) ⊆ E.rectVertices a b c d ∧ p < mu.real (E.rectSideConnectionEvent a b c d (top : Set V) (E.rectTopBoundaryVertices a b c d)) ∧ (left : Set V) ⊆ E.rectVertices a b c d ∧ p < mu.real (E.rectSideConnectionEvent a b c d (left : Set V) (E.rectLeftBoundaryVertices a b c d)) ∧ (right : Set V) ⊆ E.rectVertices a b c d ∧ p < mu.real (E.rectSideConnectionEvent a b c d (right : Set V) (E.rectRightBoundaryVertices a b c d)) ∧ let template := P.fourBoundaryComponentTemplate bottom top left right (template : Set V) ⊆ E.rectVertices a b c d ∧ p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V) (E.rectBottomBoundaryVertices a b c d)) ∧ p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V) (E.rectTopBoundaryVertices a b c d)) ∧ p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V) (E.rectLeftBoundaryVertices a b c d)) ∧ p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V) (E.rectRightBoundaryVertices a b c d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_sharedEndpointComponents E mu hTI family verticalMargin horizontalMargin a b c d hbottomWidth htopWidth hbottomHeight htopHeight hleftWidth hrightWidth hleftHeight hrightHeight

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandFamily.commonBoundaryScores](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma commonBoundaryScores_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {p : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (horizontalMargin verticalMargin width height : Nat)
  (hleftBottom : (family.radiusLeft horizontalMargin : Int) + family.baseLeft 1 ≤ family.baseBottom 1 + verticalMargin)
  (hrightBottom : (family.radiusRight horizontalMargin : Int) + family.baseRight 1 ≤ family.baseBottom 1 + verticalMargin)
  (hleftTop : (family.radiusLeft horizontalMargin : Int) + family.baseTop 1 ≤ family.baseLeft 1 + verticalMargin)
  (hrightTop : (family.radiusRight horizontalMargin : Int) + family.baseTop 1 ≤ family.baseRight 1 + verticalMargin)
  (hbottomLeft : (family.radiusBottom verticalMargin : Int) + family.baseBottom 0 ≤ family.baseLeft 0 + horizontalMargin)
  (htopLeft : (family.radiusTop verticalMargin : Int) + family.baseTop 0 ≤ family.baseLeft 0 + horizontalMargin)
  (hbottomRight : (family.radiusBottom verticalMargin : Int) + family.baseRight 0 ≤ family.baseBottom 0 + horizontalMargin)
  (htopRight : (family.radiusTop verticalMargin : Int) + family.baseRight 0 ≤ family.baseTop 0 + horizontalMargin) :
-- imply
  let gridBase : Site 2 := fun i ↦ if i = 0 then family.baseLeft 0 + horizontalMargin else family.baseBottom 1 + verticalMargin let b : Int := gridBase 0 + width - (family.baseRight 0 - horizontalMargin) let d : Int := gridBase 1 + height - (family.baseTop 1 - verticalMargin) ((family.radiusLeft horizontalMargin : Int) ≤ b) → ((family.radiusRight horizontalMargin : Int) ≤ b) → ((family.radiusBottom verticalMargin : Int) ≤ d) → ((family.radiusTop verticalMargin : Int) ≤ d) → (0 : Real) ≤ b ∧ (0 : Real) ≤ d ∧ (∀ i : Fin (width + 1), p < mu.real (E.rectSideConnectionEvent 0 b 0 d (P.shift (gridBase + preferenceGridSite (i, (0 : Fin (height + 1)))) '' (S : Set V)) (E.rectBottomBoundaryVertices 0 b 0 d))) ∧ (∀ i : Fin (width + 1), p < mu.real (E.rectSideConnectionEvent 0 b 0 d (P.shift (gridBase + preferenceGridSite (i, Fin.last height)) '' (S : Set V)) (E.rectTopBoundaryVertices 0 b 0 d))) ∧ (∀ j : Fin (height + 1), p < mu.real (E.rectSideConnectionEvent 0 b 0 d (P.shift (gridBase + preferenceGridSite ((0 : Fin (width + 1)), j)) '' (S : Set V)) (E.rectLeftBoundaryVertices 0 b 0 d))) ∧ (∀ j : Fin (height + 1), p < mu.real (E.rectSideConnectionEvent 0 b 0 d (P.shift (gridBase + preferenceGridSite (Fin.last width, j)) '' (S : Set V)) (E.rectRightBoundaryVertices 0 b 0 d))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandFamily.commonBoundaryScores E mu hTI family horizontalMargin verticalMargin width height hleftBottom hrightBottom hleftTop hrightTop hbottomLeft htopLeft hbottomRight htopRight

/--
[PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.bottomBandScore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma bottomBandScore_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {margin M : Nat}
  {p : Real}
  {data : E.CommonSquareNormalBoundaryBandData mu S margin M p}
  {v : PreferenceGridVertex width height}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (width height : Nat)
  (hv : v.2.val ≤ margin) :
-- imply
  p < mu.real (E.rectSideConnectionEvent (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real) ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image (P.shift (preferenceGridSite v)) : Set V) (E.rectBottomBoundaryVertices (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.bottomBandScore E mu hTI data width height v hv

/--
[PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.topBandScore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma topBandScore_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {margin M : Nat}
  {p : Real}
  {data : E.CommonSquareNormalBoundaryBandData mu S margin M p}
  {v : PreferenceGridVertex width height}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (width height : Nat)
  (hv : height ≤ v.2.val + margin) :
-- imply
  p < mu.real (E.rectSideConnectionEvent (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real) ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image (P.shift (preferenceGridSite v)) : Set V) (E.rectTopBoundaryVertices (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.topBandScore E mu hTI data width height v hv

/--
[PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.leftBandScore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma leftBandScore_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {margin M : Nat}
  {p : Real}
  {data : E.CommonSquareNormalBoundaryBandData mu S margin M p}
  {v : PreferenceGridVertex width height}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (width height : Nat)
  (hv : v.1.val ≤ margin) :
-- imply
  p < mu.real (E.rectSideConnectionEvent (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real) ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image (P.shift (preferenceGridSite v)) : Set V) (E.rectLeftBoundaryVertices (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.leftBandScore E mu hTI data width height v hv

/--
[PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.rightBandScore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma rightBandScore_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {margin M : Nat}
  {p : Real}
  {data : E.CommonSquareNormalBoundaryBandData mu S margin M p}
  {v : PreferenceGridVertex width height}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (width height : Nat)
  (hv : width ≤ v.1.val + margin) :
-- imply
  p < mu.real (E.rectSideConnectionEvent (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real) ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image (P.shift (preferenceGridSite v)) : Set V) (E.rectRightBoundaryVertices (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.rightBandScore E mu hTI data width height v hv

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_commonBoundaryBandScores](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_commonBoundaryBandScores_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {p : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (squareRequirement margin width height : Nat) :
-- imply
  ∃ M, ∃ data : E.CommonSquareNormalBoundaryBandData mu S margin M p, squareRequirement ≤ M ∧ (let template := P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop (∀ v : PreferenceGridVertex width height, (template.image (P.shift (preferenceGridSite v)) : Set V) ⊆ E.rectVertices (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real)) ∧ (∀ v : PreferenceGridVertex width height, v.2.val ≤ margin → p < mu.real (E.rectSideConnectionEvent (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real) (template.image (P.shift (preferenceGridSite v)) : Set V) (E.rectBottomBoundaryVertices (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real)))) ∧ (∀ v : PreferenceGridVertex width height, height ≤ v.2.val + margin → p < mu.real (E.rectSideConnectionEvent (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real) (template.image (P.shift (preferenceGridSite v)) : Set V) (E.rectTopBoundaryVertices (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real)))) ∧ (∀ v : PreferenceGridVertex width height, v.1.val ≤ margin → p < mu.real (E.rectSideConnectionEvent (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real) (template.image (P.shift (preferenceGridSite v)) : Set V) (E.rectLeftBoundaryVertices (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real)))) ∧ (∀ v : PreferenceGridVertex width height, width ≤ v.1.val + margin → p < mu.real (E.rectSideConnectionEvent (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real) (template.image (P.shift (preferenceGridSite v)) : Set V) (E.rectRightBoundaryVertices (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real))))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_commonBoundaryBandScores E mu hTI family squareRequirement margin width height

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_fullAlternatingMargins](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_fullAlternatingMargins_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {S : Finset V}
  {p : Real}
  {family : E.NormalBoundaryBandFamily mu S p} :
-- imply
  ∃ horizontal vertical : Nat → Nat, Tendsto horizontal atTop atTop ∧ Tendsto vertical atTop atTop ∧ (∀ n, (family.radiusLeft (horizontal n) : Int) + family.baseLeft 1 ≤ family.baseBottom 1 + vertical n) ∧ (∀ n, (family.radiusRight (horizontal n) : Int) + family.baseRight 1 ≤ family.baseBottom 1 + vertical n) ∧ (∀ n, (family.radiusLeft (horizontal n) : Int) + family.baseTop 1 ≤ family.baseLeft 1 + vertical n) ∧ (∀ n, (family.radiusRight (horizontal n) : Int) + family.baseTop 1 ≤ family.baseRight 1 + vertical n) ∧ (∀ n, (family.radiusBottom (vertical n) : Int) + family.baseBottom 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧ (∀ n, (family.radiusTop (vertical n) : Int) + family.baseTop 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧ (∀ n, (family.radiusBottom (vertical n) : Int) + family.baseRight 0 ≤ family.baseBottom 0 + horizontal (n + 1)) ∧ (∀ n, (family.radiusTop (vertical n) : Int) + family.baseRight 0 ≤ family.baseTop 0 + horizontal (n + 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_fullAlternatingMargins E family

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_alternatingMargins_with_requirements](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_alternatingMargins_with_requirements_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {S : Finset V}
  {p : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
-- given
  (verticalRequirement horizontalRequirement : Nat → Nat) :
-- imply
  ∃ horizontal vertical : Nat → Nat, Tendsto horizontal atTop atTop ∧ Tendsto vertical atTop atTop ∧ (∀ n, verticalRequirement (horizontal n) ≤ vertical n) ∧ (∀ n, horizontalRequirement (vertical n) ≤ horizontal (n + 1)) ∧ (∀ n, (family.radiusLeft (horizontal n) : Int) + family.baseLeft 1 ≤ family.baseBottom 1 + vertical n) ∧ (∀ n, (family.radiusRight (horizontal n) : Int) + family.baseRight 1 ≤ family.baseBottom 1 + vertical n) ∧ (∀ n, (family.radiusBottom (vertical n) : Int) + family.baseBottom 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧ (∀ n, (family.radiusTop (vertical n) : Int) + family.baseTop 0 ≤ family.baseLeft 0 + horizontal (n + 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_alternatingMargins_with_requirements E family verticalRequirement horizontalRequirement

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_fullAlternatingMargins_with_requirements](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_fullAlternatingMargins_with_requirements_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {S : Finset V}
  {p : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
-- given
  (verticalRequirement horizontalRequirement : Nat → Nat) :
-- imply
  ∃ horizontal vertical : Nat → Nat, Tendsto horizontal atTop atTop ∧ Tendsto vertical atTop atTop ∧ (∀ n, verticalRequirement (horizontal n) ≤ vertical n) ∧ (∀ n, horizontalRequirement (vertical n) ≤ horizontal (n + 1)) ∧ (∀ n, (family.radiusLeft (horizontal n) : Int) + family.baseLeft 1 ≤ family.baseBottom 1 + vertical n) ∧ (∀ n, (family.radiusRight (horizontal n) : Int) + family.baseRight 1 ≤ family.baseBottom 1 + vertical n) ∧ (∀ n, (family.radiusLeft (horizontal n) : Int) + family.baseTop 1 ≤ family.baseLeft 1 + vertical n) ∧ (∀ n, (family.radiusRight (horizontal n) : Int) + family.baseTop 1 ≤ family.baseRight 1 + vertical n) ∧ (∀ n, (family.radiusBottom (vertical n) : Int) + family.baseBottom 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧ (∀ n, (family.radiusTop (vertical n) : Int) + family.baseTop 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧ (∀ n, (family.radiusBottom (vertical n) : Int) + family.baseRight 0 ≤ family.baseBottom 0 + horizontal (n + 1)) ∧ (∀ n, (family.radiusTop (vertical n) : Int) + family.baseRight 0 ≤ family.baseTop 0 + horizontal (n + 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_fullAlternatingMargins_with_requirements E family verticalRequirement horizontalRequirement

/--
[PeriodicPlaneEmbedding.orbitBoxCoordinateBound_le_connectorMarginRequirement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma orbitBoxCoordinateBound_le_connectorMarginRequirement_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {radius : Nat}
  {i : Fin 2} :
-- imply
  E.orbitBoxCoordinateBound (P.bufferedRadius radius) i ≤ E.connectorMarginRequirement radius := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.orbitBoxCoordinateBound_le_connectorMarginRequirement E radius i

/--
[PeriodicPlaneEmbedding.orbitBox_subset_connectorMarginSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma orbitBox_subset_connectorMarginSquare_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {radius : Nat} :
-- imply
  (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆ E.rectVertices (-(E.connectorMarginRequirement radius : Real)) (E.connectorMarginRequirement radius) (-(E.connectorMarginRequirement radius : Real)) (E.connectorMarginRequirement radius) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.orbitBox_subset_connectorMarginSquare E radius

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_fullAlternatingMargins_with_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_fullAlternatingMargins_with_connector_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {S : Finset V}
  {p : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {radius : Nat} :
-- imply
  ∃ horizontal vertical : Nat → Nat, Tendsto horizontal atTop atTop ∧ Tendsto vertical atTop atTop ∧ (∀ n, E.connectorMarginRequirement radius ≤ vertical n) ∧ (∀ n, E.connectorMarginRequirement radius ≤ horizontal (n + 1)) ∧ (∀ n, (family.radiusLeft (horizontal n) : Int) + family.baseLeft 1 ≤ family.baseBottom 1 + vertical n) ∧ (∀ n, (family.radiusRight (horizontal n) : Int) + family.baseRight 1 ≤ family.baseBottom 1 + vertical n) ∧ (∀ n, (family.radiusLeft (horizontal n) : Int) + family.baseTop 1 ≤ family.baseLeft 1 + vertical n) ∧ (∀ n, (family.radiusRight (horizontal n) : Int) + family.baseTop 1 ≤ family.baseRight 1 + vertical n) ∧ (∀ n, (family.radiusBottom (vertical n) : Int) + family.baseBottom 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧ (∀ n, (family.radiusTop (vertical n) : Int) + family.baseTop 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧ (∀ n, (family.radiusBottom (vertical n) : Int) + family.baseRight 0 ≤ family.baseBottom 0 + horizontal (n + 1)) ∧ (∀ n, (family.radiusTop (vertical n) : Int) + family.baseRight 0 ≤ family.baseTop 0 + horizontal (n + 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_fullAlternatingMargins_with_connector E family radius

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandFamily.alignedMarginSchedule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma alignedMarginSchedule_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {S : Finset V}
  {p : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
-- given
  (verticalRequirement horizontalRequirement : Nat → Nat) :
-- imply
  family.AlignedMarginSchedule E verticalRequirement horizontalRequirement := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandFamily.alignedMarginSchedule E family verticalRequirement horizontalRequirement

/--
[PeriodicPlaneEmbedding.exists_cofinalNormalBoundaryBandFamilies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_cofinalNormalBoundaryBandFamilies_eq
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
  ∃ (p : Nat → Real) (family : ∀ m, E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)), Tendsto p atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_cofinalNormalBoundaryBandFamilies E mu hFKG hTI hunique

/--
[PeriodicPlaneEmbedding.exists_cofinalNormalBoundaryBandFamilies_with_connectorSchedule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_cofinalNormalBoundaryBandFamilies_with_connectorSchedule_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {radius : Nat → Nat}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  ∃ (p : Nat → Real) (family : ∀ m, E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)), Tendsto p atTop (nhds 1) ∧ ∀ m, (family m).AlignedMarginSchedule E (fun _ ↦ E.connectorMarginRequirement (radius m)) (fun _ ↦ E.connectorMarginRequirement (radius m)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_cofinalNormalBoundaryBandFamilies_with_connectorSchedule E mu hFKG hTI hunique radius

/--
[PeriodicPlaneEmbedding.exists_uniformTemplateBoundaryBandCrossingRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_uniformTemplateBoundaryBandCrossingRadius_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {template : Nat → Finset V}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (htemplateHit : Tendsto (fun n ↦ mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1)) :
-- imply
  ∃ radius, E.UniformTemplateBoundaryBandCrossingRadius mu template radius := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplateBoundaryBandCrossingRadius E mu hFKG hTI hunique template htemplateHit

/--
[PeriodicPlaneEmbedding.exists_uniformBoundaryBandRadius_with_cofinalConnectorSchedule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_uniformBoundaryBandRadius_with_cofinalConnectorSchedule_eq
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
  ∃ (radius : Nat → Nat) (p : Nat → Real) (family : ∀ m, E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)), E.UniformBoundaryBandCrossingRadius mu radius ∧ Tendsto p atTop (nhds 1) ∧ ∀ m, (family m).AlignedMarginSchedule E (fun _ ↦ E.connectorMarginRequirement (radius m)) (fun _ ↦ E.connectorMarginRequirement (radius m)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformBoundaryBandRadius_with_cofinalConnectorSchedule E mu hFKG hTI hunique

/--
[PeriodicPlaneEmbedding.exists_alignedActiveSide_choice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_alignedActiveSide_choice_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {S : Nat → Finset V}
  {p : Nat → Real}
  {cutoff : Nat}
  {epsilon : Real}
-- given
  (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
  (hp : Tendsto p atTop (nhds 1))
  (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ m, cutoff ≤ m ∧ 1 - epsilon < p m ∧ (family m).AlignedMarginSchedule E (verticalRequirement m) (horizontalRequirement m) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_alignedActiveSide_choice E mu S p family hp verticalRequirement horizontalRequirement cutoff hepsilon

/--
[PeriodicPlaneEmbedding.exists_uniformRadius_alignedActiveSide_choice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_uniformRadius_alignedActiveSide_choice_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {S : Nat → Finset V}
  {p : Nat → Real}
  {radius : Nat → Nat}
  {cutoff : Nat}
  {epsilon : Real}
-- given
  (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
  (hp : Tendsto p atTop (nhds 1))
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ m, cutoff ≤ m ∧ 1 - epsilon < p m ∧ (family m).AlignedMarginSchedule E (fun _ ↦ E.connectorMarginRequirement (radius m)) (fun _ ↦ E.connectorMarginRequirement (radius m)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformRadius_alignedActiveSide_choice E mu S p family hp radius cutoff hepsilon

/--
[PeriodicGraph.exists_commonBoundaryPairMergeRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_commonBoundaryPairMergeRadius_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {bottom top left right : Finset V}
  {cutoff : Nat}
  {epsilon : Real}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ radius, cutoff ≤ radius ∧ mu.real (P.pairMergeErrorUnion bottom top radius) < epsilon ∧ mu.real (P.pairMergeErrorUnion left right radius) < epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_commonBoundaryPairMergeRadius P mu hunique bottom top left right cutoff hepsilon

/--
[PeriodicPlaneEmbedding.exists_alignedSharedLevel_choice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_alignedSharedLevel_choice_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Nat → Finset V}
  {p : Nat → Real}
  {scaleCutoff : Nat}
  {connectorRadius : Nat → Nat}
  {epsilon : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
  (hp : Tendsto p atTop (nhds 1))
  (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ m extent : Nat, ∃ bottom top left right : Finset V, scaleCutoff ≤ m ∧ 1 - epsilon < p m ∧ (family m).AlignedMarginSchedule E (verticalRequirement m) (horizontalRequirement m) ∧ (P.orbitBox (P.bufferedRadius (connectorRadius m)) : Set V) ⊆ E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent ∧ (bottom : Set V) ⊆ E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent ∧ p m < mu.real (E.rectSideConnectionEvent (-(extent : Real)) extent (-(extent : Real)) extent (bottom : Set V) (E.rectBottomBoundaryVertices (-(extent : Real)) extent (-(extent : Real)) extent)) ∧ (top : Set V) ⊆ E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent ∧ p m < mu.real (E.rectSideConnectionEvent (-(extent : Real)) extent (-(extent : Real)) extent (top : Set V) (E.rectTopBoundaryVertices (-(extent : Real)) extent (-(extent : Real)) extent)) ∧ (left : Set V) ⊆ E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent ∧ p m < mu.real (E.rectSideConnectionEvent (-(extent : Real)) extent (-(extent : Real)) extent (left : Set V) (E.rectLeftBoundaryVertices (-(extent : Real)) extent (-(extent : Real)) extent)) ∧ (right : Set V) ⊆ E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent ∧ p m < mu.real (E.rectSideConnectionEvent (-(extent : Real)) extent (-(extent : Real)) extent (right : Set V) (E.rectRightBoundaryVertices (-(extent : Real)) extent (-(extent : Real)) extent)) ∧ let template := P.fourBoundaryComponentTemplate bottom top left right (template : Set V) ⊆ E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent ∧ p m < mu.real (E.rectSideConnectionEvent (-(extent : Real)) extent (-(extent : Real)) extent (template : Set V) (E.rectBottomBoundaryVertices (-(extent : Real)) extent (-(extent : Real)) extent)) ∧ p m < mu.real (E.rectSideConnectionEvent (-(extent : Real)) extent (-(extent : Real)) extent (template : Set V) (E.rectTopBoundaryVertices (-(extent : Real)) extent (-(extent : Real)) extent)) ∧ p m < mu.real (E.rectSideConnectionEvent (-(extent : Real)) extent (-(extent : Real)) extent (template : Set V) (E.rectLeftBoundaryVertices (-(extent : Real)) extent (-(extent : Real)) extent)) ∧ p m < mu.real (E.rectSideConnectionEvent (-(extent : Real)) extent (-(extent : Real)) extent (template : Set V) (E.rectRightBoundaryVertices (-(extent : Real)) extent (-(extent : Real)) extent)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_alignedSharedLevel_choice E mu hTI S p family hp verticalRequirement horizontalRequirement scaleCutoff connectorRadius hepsilon

/--
[PeriodicPlaneEmbedding.exists_alignedSharedLevel_with_nextConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_alignedSharedLevel_with_nextConnector_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Nat → Finset V}
  {p : Nat → Real}
  {scaleCutoff connectorRadius : Nat}
  {scoreEpsilon mergeEpsilon : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
  (hp : Tendsto p atTop (nhds 1))
  (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
  (hscoreEpsilon : 0 < scoreEpsilon)
  (hmergeEpsilon : 0 < mergeEpsilon) :
-- imply
  ∃ m extent : Nat, ∃ bottom top left right : Finset V, ∃ nextConnector : Nat, scaleCutoff ≤ m ∧ connectorRadius ≤ nextConnector ∧ 1 - scoreEpsilon < p m ∧ (family m).AlignedMarginSchedule E (verticalRequirement m) (horizontalRequirement m) ∧ (P.orbitBox (P.bufferedRadius connectorRadius) : Set V) ⊆ E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent ∧ (bottom : Set V) ⊆ E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent ∧ p m < mu.real (E.rectSideConnectionEvent (-(extent : Real)) extent (-(extent : Real)) extent (bottom : Set V) (E.rectBottomBoundaryVertices (-(extent : Real)) extent (-(extent : Real)) extent)) ∧ (top : Set V) ⊆ E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent ∧ p m < mu.real (E.rectSideConnectionEvent (-(extent : Real)) extent (-(extent : Real)) extent (top : Set V) (E.rectTopBoundaryVertices (-(extent : Real)) extent (-(extent : Real)) extent)) ∧ (left : Set V) ⊆ E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent ∧ p m < mu.real (E.rectSideConnectionEvent (-(extent : Real)) extent (-(extent : Real)) extent (left : Set V) (E.rectLeftBoundaryVertices (-(extent : Real)) extent (-(extent : Real)) extent)) ∧ (right : Set V) ⊆ E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent ∧ p m < mu.real (E.rectSideConnectionEvent (-(extent : Real)) extent (-(extent : Real)) extent (right : Set V) (E.rectRightBoundaryVertices (-(extent : Real)) extent (-(extent : Real)) extent)) ∧ (let template := P.fourBoundaryComponentTemplate bottom top left right (template : Set V) ⊆ E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent ∧ p m < mu.real (E.rectSideConnectionEvent (-(extent : Real)) extent (-(extent : Real)) extent (template : Set V) (E.rectBottomBoundaryVertices (-(extent : Real)) extent (-(extent : Real)) extent)) ∧ p m < mu.real (E.rectSideConnectionEvent (-(extent : Real)) extent (-(extent : Real)) extent (template : Set V) (E.rectTopBoundaryVertices (-(extent : Real)) extent (-(extent : Real)) extent)) ∧ p m < mu.real (E.rectSideConnectionEvent (-(extent : Real)) extent (-(extent : Real)) extent (template : Set V) (E.rectLeftBoundaryVertices (-(extent : Real)) extent (-(extent : Real)) extent)) ∧ p m < mu.real (E.rectSideConnectionEvent (-(extent : Real)) extent (-(extent : Real)) extent (template : Set V) (E.rectRightBoundaryVertices (-(extent : Real)) extent (-(extent : Real)) extent))) ∧ mu.real (P.pairMergeErrorUnion bottom top nextConnector) < mergeEpsilon ∧ mu.real (P.pairMergeErrorUnion left right nextConnector) < mergeEpsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_alignedSharedLevel_with_nextConnector E mu hTI hunique S p family hp verticalRequirement horizontalRequirement scaleCutoff connectorRadius hscoreEpsilon hmergeEpsilon

/--
[PeriodicPlaneEmbedding.nonempty_alignedSharedLevelStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma nonempty_alignedSharedLevelStep_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Nat → Finset V}
  {p : Nat → Real}
  {previousScale previousConnector : Nat}
  {scoreEpsilon mergeEpsilon : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
  (hp : Tendsto p atTop (nhds 1))
  (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
  (hscoreEpsilon : 0 < scoreEpsilon)
  (hmergeEpsilon : 0 < mergeEpsilon) :
-- imply
  Nonempty (E.AlignedSharedLevelStep mu S p family verticalRequirement horizontalRequirement previousScale previousConnector scoreEpsilon mergeEpsilon) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.nonempty_alignedSharedLevelStep E mu hTI hunique S p family hp verticalRequirement horizontalRequirement previousScale previousConnector hscoreEpsilon hmergeEpsilon

/--
[PeriodicPlaneEmbedding.exists_recursiveAlignedSharedLevelSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_recursiveAlignedSharedLevelSteps_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Nat → Finset V}
  {p : Nat → Real}
  {scoreEpsilon mergeEpsilon : Nat → Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
  (hp : Tendsto p atTop (nhds 1))
  (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
  (hscoreEpsilon : ∀ n, 0 < scoreEpsilon n)
  (hmergeEpsilon : ∀ n, 0 < mergeEpsilon n) :
-- imply
  ∃ state : Nat → Nat × Nat, ∃ steps : ∀ n, E.AlignedSharedLevelStep mu S p family verticalRequirement horizontalRequirement (state n).1 (state n).2 (scoreEpsilon n) (mergeEpsilon n), state 0 = (0, 0) ∧ ∀ n, state (n + 1) = ((steps n).scale + 1, (steps n).nextConnector) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_recursiveAlignedSharedLevelSteps E mu hTI hunique S p family hp verticalRequirement horizontalRequirement scoreEpsilon mergeEpsilon hscoreEpsilon hmergeEpsilon

/--
[uniform_cofinal_diagonal_below_growing_cutoff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma uniform_cofinal_diagonal_below_growing_cutoff_eq
  [DecidableEq V]
  [Countable V]
  {f : Nat → Nat → Real}
  {cutoff : Nat → Nat}
-- given
  (hf : ∀ k, Tendsto (f k) atTop (nhds 1))
  (hle : ∀ k n, f k n ≤ 1) :
-- imply
  ∃ index : Nat → Nat, (∀ n, max n (cutoff n) ≤ index n) ∧ ∀ k : Nat → Nat, (∀ n, k n < n + 1) → Tendsto (fun n ↦ f (k n) (index n)) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.uniform_cofinal_diagonal_below_growing_cutoff f hf hle cutoff

/--
[exists_cofinalIndex_uniform_tendsto_one_below_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_cofinalIndex_uniform_tendsto_one_below_diagonal_eq
  [DecidableEq V]
  [Countable V]
  {f : Nat → Nat → Real}
-- given
  (hf : ∀ k, Tendsto (f k) atTop (nhds 1))
  (hle : ∀ k n, f k n ≤ 1) :
-- imply
  ∃ index : Nat → Nat, (∀ n, n ≤ index n) ∧ ∀ k : Nat → Nat, (∀ n, k n < n + 1) → Tendsto (fun n ↦ f (k n) (index n)) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_cofinalIndex_uniform_tendsto_one_below_diagonal f hf hle

/--
[PeriodicPlaneEmbedding.verticalCrossing_tendsto_one_of_boundaryScores](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma verticalCrossing_tendsto_one_of_boundaryScores_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Nat → Real}
  {bottomSource topSource : Nat → Finset V}
-- given
  (hFKG : IsFKG mu)
  (hbottom : Tendsto (fun n ↦ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (bottomSource n : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) atTop (nhds 1))
  (htop : Tendsto (fun n ↦ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (topSource n : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) atTop (nhds 1))
  (hmerge : Tendsto (fun n ↦ mu.real (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n) (bottomSource n) (topSource n))) atTop (nhds 0)) :
-- imply
  Tendsto (fun n ↦ mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossing_tendsto_one_of_boundaryScores E mu hFKG a b c d bottomSource topSource hbottom htop hmerge

/--
[PeriodicPlaneEmbedding.horizontalCrossing_tendsto_one_of_boundaryScores](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma horizontalCrossing_tendsto_one_of_boundaryScores_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Nat → Real}
  {leftSource rightSource : Nat → Finset V}
-- given
  (hFKG : IsFKG mu)
  (hleft : Tendsto (fun n ↦ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (leftSource n : Set V) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) atTop (nhds 1))
  (hright : Tendsto (fun n ↦ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (rightSource n : Set V) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) atTop (nhds 1))
  (hmerge : Tendsto (fun n ↦ mu.real (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n) (leftSource n) (rightSource n))) atTop (nhds 0)) :
-- imply
  Tendsto (fun n ↦ mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossing_tendsto_one_of_boundaryScores E mu hFKG a b c d leftSource rightSource hleft hright hmerge

/--
[PeriodicPlaneEmbedding.preferenceGrid_orbitBox_subset_translated_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma preferenceGrid_orbitBox_subset_translated_rect_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2}
-- given
  (R M width height : Nat)
  (hx : E.orbitBoxCoordinateBound R (0 : Fin 2) ≤ M)
  (hy : E.orbitBoxCoordinateBound R (1 : Fin 2) ≤ M) :
-- imply
  ∀ v : PreferenceGridVertex width height, P.shift (preferenceGridSite v + z) '' (P.orbitBox R : Set V) ⊆ E.rectVertices (-(M : Real) + z 0) (M + width + z 0 : Real) (-(M : Real) + z 1) (M + height + z 1 : Real) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.preferenceGrid_orbitBox_subset_translated_rect E R M width height z hx hy

/--
[PeriodicPlaneEmbedding.exists_fourShiftTemplate_outward_crossing_max_tendsto_one_of_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_fourShiftTemplate_outward_crossing_max_tendsto_one_of_connector_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {M : Nat → Nat}
  {zLeft zRight zBottom zTop : Nat → Site 2}
  {pad : Nat → Int}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hleft : ∀ n, ((P.orbitBox n).image (P.shift (zLeft n)) : Set V) ⊆ E.rectVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real))
  (hright : ∀ n, ((P.orbitBox n).image (P.shift (zRight n)) : Set V) ⊆ E.rectVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real))
  (hbottom : ∀ n, ((P.orbitBox n).image (P.shift (zBottom n)) : Set V) ⊆ E.rectVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real))
  (htop : ∀ n, ((P.orbitBox n).image (P.shift (zTop n)) : Set V) ⊆ E.rectVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real))
  (hleftLimit : Tendsto (fun n ↦ mu.real (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real) ((P.orbitBox n).image (P.shift (zLeft n)) : Set V) (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
  (hrightLimit : Tendsto (fun n ↦ mu.real (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real) ((P.orbitBox n).image (P.shift (zRight n)) : Set V) (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
  (hbottomLimit : Tendsto (fun n ↦ mu.real (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real) ((P.orbitBox n).image (P.shift (zBottom n)) : Set V) (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
  (htopLimit : Tendsto (fun n ↦ mu.real (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real) ((P.orbitBox n).image (P.shift (zTop n)) : Set V) (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
  (hpad : ∀ n, 0 ≤ pad n) :
-- imply
  ∃ radius : Nat → Nat, ∀ (width height : Nat → Nat) (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n), (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (preferenceGridSite v + verticalShift (-(pad n))) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (-(M n : Real)) (M n + width n : Real) (-(M n : Real) - pad n) (M n + height n - pad n : Real)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (preferenceGridSite v + verticalShift (-(pad n))) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (-(M n : Real)) (M n + width n : Real) (-(M n : Real) - pad n) (M n + height n + pad n : Real)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (preferenceGridSite v + horizontalShift (-(pad n))) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (-(M n : Real) - pad n) (M n + width n - pad n : Real) (-(M n : Real)) (M n + height n : Real)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (preferenceGridSite v + horizontalShift (-(pad n))) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (-(M n : Real) - pad n) (M n + width n + pad n : Real) (-(M n : Real)) (M n + height n : Real)) → Tendsto (fun n ↦ max (mu.real (E.verticalCrossingEvent (-(M n : Real)) (M n + width n : Real) (-(M n : Real) - pad n) (M n + height n + pad n : Real))) (mu.real (E.horizontalCrossingEvent (-(M n : Real) - pad n) (M n + width n + pad n : Real) (-(M n : Real)) (M n + height n : Real)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_fourShiftTemplate_outward_crossing_max_tendsto_one_of_connector E mu hFKG hTI hunique M zLeft zRight zBottom zTop hleft hright hbottom htop hleftLimit hrightLimit hbottomLimit htopLimit pad hpad

/--
[PeriodicPlaneEmbedding.exists_fourShiftTemplate_outward_crossing_max_tendsto_one_of_coordinateBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma exists_fourShiftTemplate_outward_crossing_max_tendsto_one_of_coordinateBounds_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {M : Nat → Nat}
  {zLeft zRight zBottom zTop : Nat → Site 2}
  {pad : Nat → Int}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hleft : ∀ n, ((P.orbitBox n).image (P.shift (zLeft n)) : Set V) ⊆ E.rectVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real))
  (hright : ∀ n, ((P.orbitBox n).image (P.shift (zRight n)) : Set V) ⊆ E.rectVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real))
  (hbottom : ∀ n, ((P.orbitBox n).image (P.shift (zBottom n)) : Set V) ⊆ E.rectVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real))
  (htop : ∀ n, ((P.orbitBox n).image (P.shift (zTop n)) : Set V) ⊆ E.rectVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real))
  (hleftLimit : Tendsto (fun n ↦ mu.real (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real) ((P.orbitBox n).image (P.shift (zLeft n)) : Set V) (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
  (hrightLimit : Tendsto (fun n ↦ mu.real (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real) ((P.orbitBox n).image (P.shift (zRight n)) : Set V) (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
  (hbottomLimit : Tendsto (fun n ↦ mu.real (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real) ((P.orbitBox n).image (P.shift (zBottom n)) : Set V) (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
  (htopLimit : Tendsto (fun n ↦ mu.real (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real) ((P.orbitBox n).image (P.shift (zTop n)) : Set V) (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
  (hpad : ∀ n, 0 ≤ pad n) :
-- imply
  ∃ radius : Nat → Nat, ∀ (width height : Nat → Nat) (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n), (∀ n, E.orbitBoxCoordinateBound (P.bufferedRadius (radius n)) (0 : Fin 2) ≤ M n) → (∀ n, E.orbitBoxCoordinateBound (P.bufferedRadius (radius n)) (1 : Fin 2) ≤ M n) → Tendsto (fun n ↦ max (mu.real (E.verticalCrossingEvent (-(M n : Real)) (M n + width n : Real) (-(M n : Real) - pad n) (M n + height n + pad n : Real))) (mu.real (E.horizontalCrossingEvent (-(M n : Real) - pad n) (M n + width n + pad n : Real) (-(M n : Real)) (M n + height n : Real)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_fourShiftTemplate_outward_crossing_max_tendsto_one_of_coordinateBounds E mu hFKG hTI hunique M zLeft zRight zBottom zTop hleft hright hbottom htop hleftLimit hrightLimit hbottomLimit htopLimit pad hpad

/--
[adjacent_height_array_contradiction_of_primal_dual_bounded_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma adjacent_height_array_contradiction_of_primal_dual_bounded_limits_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {K : Nat → Nat}
-- given
  (horizontal vertical dualVertical dualHorizontal : Nat → Nat → Real)
  (hhorizontal_nonneg : ∀ n k, 0 ≤ horizontal n k)
  (hvertical_nonneg : ∀ n k, 0 ≤ vertical n k)
  (hhorizontal_le_one : ∀ n k, horizontal n k ≤ 1)
  (hvertical_le_one : ∀ n k, vertical n k ≤ 1)
  (hvertical_start : Tendsto (fun n ↦ vertical n 0) atTop (nhds 1))
  (hhorizontal_end : Tendsto (fun n ↦ horizontal n (K n + 1)) atTop (nhds 1))
  (hmatchHorizontal : ∀ n k, horizontal n k + dualVertical n k ≤ 1)
  (hmatchVertical : ∀ n k, vertical n k + dualHorizontal n k ≤ 1)
  (hprimalLimits : ∀ k : Nat → Nat, (∀ n, k n < K n + 1) → Tendsto (fun n ↦ max (horizontal n (k n)) (vertical n (k n + 1))) atTop (nhds 1))
  (hdualLimits : ∀ k : Nat → Nat, (∀ n, k n ≤ K n + 1) → Tendsto (fun n ↦ max (dualVertical n (k n)) (dualHorizontal n (k n))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.adjacent_height_array_contradiction_of_primal_dual_bounded_limits horizontal vertical dualVertical dualHorizontal K hhorizontal_nonneg hvertical_nonneg hhorizontal_le_one hvertical_le_one hvertical_start hhorizontal_end hmatchHorizontal hmatchVertical hprimalLimits hdualLimits

/--
[PeriodicPlanarDualPair.adjacent_rectangles_contradiction_of_bounded_max_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma adjacent_rectangles_contradiction_of_bounded_max_limits_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {a b c d : Nat → Nat → Real}
  {K : Nat → Nat}
-- given
  (hBpos : 0 < B)
  (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
  (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
  (hspanX : ∀ n k, a n k + 5 * B < b n k - 5 * B)
  (hspanY : ∀ n k, c n k + 5 * B < d n k - 5 * B)
  (hverticalStart : Tendsto (fun n ↦ mu.real (D.primalEmbedding.verticalCrossingEvent (a n 0 + 4 * B) (b n 0 - 4 * B) (c n 0) (d n 0))) atTop (nhds 1))
  (hhorizontalEnd : Tendsto (fun n ↦ mu.real (D.primalEmbedding.horizontalCrossingEvent (a n (K n + 1)) (b n (K n + 1)) (c n (K n + 1) + 4 * B) (d n (K n + 1) - 4 * B))) atTop (nhds 1))
  (hprimal : ∀ k : Nat → Nat, (∀ n, k n < K n + 1) → Tendsto (fun n ↦ max (mu.real (D.primalEmbedding.horizontalCrossingEvent (a n (k n)) (b n (k n)) (c n (k n) + 4 * B) (d n (k n) - 4 * B))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a n (k n + 1) + 4 * B) (b n (k n + 1) - 4 * B) (c n (k n + 1)) (d n (k n + 1))))) atTop (nhds 1))
  (hdual : ∀ k : Nat → Nat, (∀ n, k n ≤ K n + 1) → Tendsto (fun n ↦ max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a n (k n) + 4 * B) (b n (k n) - 4 * B) (c n (k n)) (d n (k n)))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a n (k n)) (b n (k n)) (c n (k n) + 4 * B) (d n (k n) - 4 * B)))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.adjacent_rectangles_contradiction_of_bounded_max_limits D mu hBpos hBp hBd a b c d K hspanX hspanY hverticalStart hhorizontalEnd hprimal hdual

/--
[PeriodicPlanarDualPair.RecursiveRectangleArrayCertificate.false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma false_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {data : D.RecursiveRectangleArrayCertificate mu} :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.RecursiveRectangleArrayCertificate.false D mu data

/--
[PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_recursiveArray](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_recursiveArray_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (harray : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1 → Nonempty (D.RecursiveRectangleArrayCertificate mu)) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_recursiveArray D hp hp1 hq harray

/--
[PeriodicPlanarDualPair.MacroArrayCertificate.false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma false_eq_2
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {data : D.MacroArrayCertificate mu} :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.MacroArrayCertificate.false D mu data

/--
[PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_macroArray](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_macroArray_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (harray : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1 → Nonempty (D.MacroArrayCertificate mu)) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_macroArray D hp hp1 hq harray

/--
[PeriodicPlanarDualPair.PointwiseMacroArrayCertificate.toMacroArrayCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma toMacroArrayCertificate_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {raw : D.PointwiseMacroArrayCertificate mu} :
-- imply
  Nonempty (D.MacroArrayCertificate mu) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.PointwiseMacroArrayCertificate.toMacroArrayCertificate D mu raw

/--
[PeriodicPlanarDualPair.TwoLevelBoundaryScoreArray.false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma false_eq_3
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {data : D.TwoLevelBoundaryScoreArray mu B}
-- given
  (hFKG : IsFKG mu) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.TwoLevelBoundaryScoreArray.false D mu hFKG data

/--
[PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_boundaryScoreArray](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_boundaryScoreArray_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (harray : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1 → ∃ B : Real, Nonempty (D.TwoLevelBoundaryScoreArray mu B)) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_boundaryScoreArray D hp hp1 hq harray


-- created on 2026-10-23
