import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceReduction
open StatMech StatMech.FrontierA


/--
[kwDetOneSubWith_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardArbitraryValenceReduction.lean)
-/
@[path]
private lemma kwDetOneSubWith_eq_eq
  [Fintype D]
  {decEq decEq' : DecidableEq D}
  {M : Matrix D D Complex} :
-- imply
  kwDetOneSubWith decEq M = kwDetOneSubWith decEq' M := by
-- proof
  apply StatMech.FrontierA.kwDetOneSubWith_eq decEq decEq' M

/--
[kacWard_allWeights_of_formalRoot_eq_evenPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardArbitraryValenceReduction.lean)
-/
@[path]
private lemma kacWard_allWeights_of_formalRoot_eq_evenPolynomial_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq G.Dart]
-- given
  (phase : G.Dart -> G.Dart -> Complex)
  (hformal : kwGraphFormalRoot G phase = kwGraphFormalEvenPolynomial G)
  (weight : Sym2 V -> Complex) :
-- imply
  (1 - kwGraphTransition G weight phase).det = (kwEvenPolynomial G weight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_allWeights_of_formalRoot_eq_evenPolynomial G phase hformal weight

/--
[kacWard_allWeights_of_unitCycleLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardArbitraryValenceReduction.lean)
-/
@[path]
private lemma kacWard_allWeights_of_unitCycleLog_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq G.Dart]
-- given
  (phase : G.Dart -> G.Dart -> Complex)
  (hunit : KWGraphUnitCycleLog G phase)
  (hdeg : forall vertex, G.degree vertex <= 3)
  (hnonsquare : forall m : Sym2 V →₀ Nat, ¬ ons_IsSquarefreeExponent m -> MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0)
  (weight : Sym2 V -> Complex) :
-- imply
  (1 - kwGraphTransition G weight phase).det = (kwEvenPolynomial G weight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_allWeights_of_unitCycleLog G phase hunit hdeg hnonsquare weight

/--
[kwAngularSplit_degree_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardArbitraryValenceReduction.lean)
-/
@[path]
private lemma kwAngularSplit_degree_le_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {p : KWDartPort G} :
-- imply
  (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).degree p <= 3 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_degree_le_three embedding p

/--
[kacWard_original_iff_angularSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardArbitraryValenceReduction.lean)
-/
@[path]
private lemma kacWard_original_iff_angularSplit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (weight : Sym2 V -> Complex) :
-- imply
  (1 - kwGraphTransition G weight embedding.turnPhase).det = (kwEvenPolynomial G weight) ^ 2 <-> (1 - kwGraphTransition (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding)).det = (kwEvenPolynomial (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwOrderedSplitWeight G weight)) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_original_iff_angularSplit embedding weight

/--
[kacWard_original_of_angularSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardArbitraryValenceReduction.lean)
-/
@[path]
private lemma kacWard_original_of_angularSplit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (weight : Sym2 V -> Complex)
  (hsplit : (1 - kwGraphTransition (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding)).det = (kwEvenPolynomial (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwOrderedSplitWeight G weight)) ^ 2) :
-- imply
  (1 - kwGraphTransition G weight embedding.turnPhase).det = (kwEvenPolynomial G weight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_original_of_angularSplit embedding weight hsplit

/--
[kacWard_original_of_angularSplit_unitCycleLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardArbitraryValenceReduction.lean)
-/
@[path]
private lemma kacWard_original_of_angularSplit_unitCycleLog_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (weight : Sym2 V -> Complex)
  (hunit : KWGraphUnitCycleLog (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwAngularSplitPhase embedding))
  (hnonsquare : forall m : Sym2 (KWDartPort G) →₀ Nat, ¬ ons_IsSquarefreeExponent m -> MvPowerSeries.coeff m (kwGraphFormalRoot (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwAngularSplitPhase embedding)) = 0) :
-- imply
  (1 - kwGraphTransition G weight embedding.turnPhase).det = (kwEvenPolynomial G weight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_original_of_angularSplit_unitCycleLog embedding weight hunit hnonsquare


-- created on 2026-10-23
