import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting.Part3
open Finset StatMech StatMech.FrontierD


/--
[finiteKeyCapacityHall_of_activeInjectiveRouting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyCapacityRouting.lean)
-/
@[path]
private lemma finiteKeyCapacityHall_of_activeInjectiveRouting_eq
  [Fintype Key]
  [DecidableEq Key]
  [DecidableRel related]
-- given
  (sourceCapacity targetCapacity : Key -> Nat)
  (related : Key -> Key -> Prop)
  (route : Key -> Key)
  (hinjective : forall first second, 0 < sourceCapacity first -> 0 < sourceCapacity second -> route first = route second -> first = second)
  (hsupported : forall key, 0 < sourceCapacity key -> related key (route key))
  (hcapacity : forall key, 0 < sourceCapacity key -> sourceCapacity key <= targetCapacity (route key)) :
-- imply
  forall sourceKeys : Finset Key, (∑ key ∈ sourceKeys, sourceCapacity key) <= ∑ key ∈ (Finset.univ.filter fun targetKey => exists sourceKey, sourceKey ∈ sourceKeys /\ related sourceKey targetKey), targetCapacity key := by
-- proof
  apply StatMech.FrontierD.finiteKeyCapacityHall_of_activeInjectiveRouting sourceCapacity targetCapacity related route hinjective hsupported hcapacity

/--
[twoCycleKeyCapacityHall_of_activeKeyFiberRoutings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyCapacityRouting.lean)
-/
@[path]
private lemma twoCycleKeyCapacityHall_of_activeKeyFiberRoutings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hroutings : SixVertexHorizontalTwoCycleActiveKeyFiberRoutings T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalTwoCycleKeyCapacityHall T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.twoCycleKeyCapacityHall_of_activeKeyFiberRoutings T middle hmiddle_pos hmiddle_lt hroutings

/--
[activeKeyFiberRoutings_of_reflexiveFiberEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyCapacityRouting.lean)
-/
@[path]
private lemma activeKeyFiberRoutings_of_reflexiveFiberEmbeddings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hembeddings : SixVertexHorizontalTwoCycleReflexiveActiveFiberEmbeddings T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalTwoCycleActiveKeyFiberRoutings T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.activeKeyFiberRoutings_of_reflexiveFiberEmbeddings T middle hmiddle_pos hmiddle_lt hembeddings

/--
[twoCycleKeyCapacityHall_of_reflexiveFiberEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyCapacityRouting.lean)
-/
@[path]
private lemma twoCycleKeyCapacityHall_of_reflexiveFiberEmbeddings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hembeddings : SixVertexHorizontalTwoCycleReflexiveActiveFiberEmbeddings T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalTwoCycleKeyCapacityHall T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.twoCycleKeyCapacityHall_of_reflexiveFiberEmbeddings T middle hmiddle_pos hmiddle_lt hembeddings

/--
[activeKeyFiberRoutings_of_injectiveKeyRoutings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyCapacityRouting.lean)
-/
@[path]
private lemma activeKeyFiberRoutings_of_injectiveKeyRoutings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hroutings : SixVertexHorizontalTwoCycleInjectiveKeyRoutings T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalTwoCycleActiveKeyFiberRoutings T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.activeKeyFiberRoutings_of_injectiveKeyRoutings T middle hmiddle_pos hmiddle_lt hroutings


-- created on 2026-10-23
