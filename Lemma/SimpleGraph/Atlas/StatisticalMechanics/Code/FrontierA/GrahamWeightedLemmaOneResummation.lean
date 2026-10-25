import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneResummation
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamLemmaOneMixedFourMass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneResummation.lean)
-/
@[path]
private lemma grahamLemmaOneMixedFourMass_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  grahamLemmaOneMixedFourMass G beta J j k l m = sourcePairDisconnSum G beta J {j, k} {k, l} k m * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.grahamLemmaOneMixedFourMass_eq G beta J j k l m

/--
[grahamLemmaOneSeparatedFourMass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneResummation.lean)
-/
@[path]
private lemma grahamLemmaOneSeparatedFourMass_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  grahamLemmaOneSeparatedFourMass G beta J j k l m = sourcePairDisconnSum G beta J {j, k} ∅ k m * sourcePairDisconnSum G beta J {k, l} ∅ k m := by
-- proof
  apply StatMech.FrontierA.grahamLemmaOneSeparatedFourMass_eq G beta J j k l m

/--
[grahamLemmaOneMixedFourMass_eq_profileMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneResummation.lean)
-/
@[path]
private lemma grahamLemmaOneMixedFourMass_eq_profileMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  grahamLemmaOneMixedFourMass G beta J j k l m = grahamLemmaOneMixedProfileMass G beta J j k l m := by
-- proof
  apply StatMech.FrontierA.grahamLemmaOneMixedFourMass_eq_profileMass G beta J j k l m

/--
[grahamLemmaOneSeparatedFourMass_eq_profileMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneResummation.lean)
-/
@[path]
private lemma grahamLemmaOneSeparatedFourMass_eq_profileMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  grahamLemmaOneSeparatedFourMass G beta J j k l m = grahamLemmaOneSeparatedProfileMass G beta J j k l m := by
-- proof
  apply StatMech.FrontierA.grahamLemmaOneSeparatedFourMass_eq_profileMass G beta J j k l m

/--
[grahamLemmaOneMixedProfileMass_eq_coefficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneResummation.lean)
-/
@[path]
private lemma grahamLemmaOneMixedProfileMass_eq_coefficient_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  grahamLemmaOneMixedProfileMass G beta J j k l m = ∑' total : G.edgeFinset -> Nat, grahamLemmaOneMixedProfileCoefficient G total j k l m * weight G beta J (ofEdgeFun G total) := by
-- proof
  apply StatMech.FrontierA.grahamLemmaOneMixedProfileMass_eq_coefficient G beta J j k l m

/--
[grahamLemmaOneSeparatedProfileMass_eq_coefficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneResummation.lean)
-/
@[path]
private lemma grahamLemmaOneSeparatedProfileMass_eq_coefficient_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  grahamLemmaOneSeparatedProfileMass G beta J j k l m = ∑' total : G.edgeFinset -> Nat, grahamLemmaOneSeparatedProfileCoefficient G total j k l m * weight G beta J (ofEdgeFun G total) := by
-- proof
  apply StatMech.FrontierA.grahamLemmaOneSeparatedProfileMass_eq_coefficient G beta J j k l m


-- created on 2026-10-23
