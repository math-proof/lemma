import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCutLatticeCounterexample.Part2
open Finset StatMech StatMech.FrontierA


/--
[grahamC4RootCutSupported_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean)
-/
@[path]
private lemma grahamC4RootCutSupported_empty_eq :
-- imply
  GrahamC4RootCutSupported ∅ := by
-- proof
  apply StatMech.FrontierA.grahamC4RootCutSupported_empty

/--
[grahamC4RootCutSupported_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean)
-/
@[path]
private lemma grahamC4RootCutSupported_one_eq :
-- imply
  GrahamC4RootCutSupported {1} := by
-- proof
  apply StatMech.FrontierA.grahamC4RootCutSupported_one

/--
[grahamC4RootCutSupported_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean)
-/
@[path]
private lemma grahamC4RootCutSupported_two_eq :
-- imply
  GrahamC4RootCutSupported {2} := by
-- proof
  apply StatMech.FrontierA.grahamC4RootCutSupported_two

/--
[not_grahamC4RootCutSupported_one_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean)
-/
@[path]
private lemma not_grahamC4RootCutSupported_one_two_eq :
-- imply
  ¬ GrahamC4RootCutSupported {1, 2} := by
-- proof
  apply StatMech.FrontierA.not_grahamC4RootCutSupported_one_two

/--
[grahamC4_rootCutSupport_not_unionClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean)
-/
@[path]
private lemma grahamC4_rootCutSupport_not_unionClosed_eq :
-- imply
  ∃ A B : Finset (Fin 4), GrahamC4RootCutSupported A /\ GrahamC4RootCutSupported B /\ GrahamC4RootCutSupported (A ∩ B) /\ ¬ GrahamC4RootCutSupported (A ∪ B) := by
-- proof
  apply StatMech.FrontierA.grahamC4_rootCutSupport_not_unionClosed

/--
[grahamC4_not_latticeCondition_of_exact_cutSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean)
-/
@[path]
private lemma grahamC4_not_latticeCondition_of_exact_cutSupport_eq
-- given
  (mu : Finset (Fin 4) -> Real)
  (hmu : ∀ S, 0 <= mu S)
  (hsupport : ∀ S, 0 < mu S <-> GrahamC4RootCutSupported S) :
-- imply
  ¬ ∀ A B : Finset (Fin 4), mu A * mu B <= mu (A ∩ B) * mu (A ∪ B) := by
-- proof
  apply StatMech.FrontierA.grahamC4_not_latticeCondition_of_exact_cutSupport mu hmu hsupport

/--
[grahamK23RootCutSupported_zero_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean)
-/
@[path]
private lemma grahamK23RootCutSupported_zero_two_eq :
-- imply
  GrahamK23RootCutSupported {0, 2} := by
-- proof
  apply StatMech.FrontierA.grahamK23RootCutSupported_zero_two

/--
[grahamK23RootCutSupported_one_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean)
-/
@[path]
private lemma grahamK23RootCutSupported_one_two_eq :
-- imply
  GrahamK23RootCutSupported {1, 2} := by
-- proof
  apply StatMech.FrontierA.grahamK23RootCutSupported_one_two

/--
[grahamK23RootCutSupported_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean)
-/
@[path]
private lemma grahamK23RootCutSupported_two_eq :
-- imply
  GrahamK23RootCutSupported {2} := by
-- proof
  apply StatMech.FrontierA.grahamK23RootCutSupported_two

/--
[not_grahamK23RootCutSupported_zero_one_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean)
-/
@[path]
private lemma not_grahamK23RootCutSupported_zero_one_two_eq :
-- imply
  ¬ GrahamK23RootCutSupported {0, 1, 2} := by
-- proof
  apply StatMech.FrontierA.not_grahamK23RootCutSupported_zero_one_two

/--
[grahamK23_pair_reaches_in_left_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean)
-/
@[path]
private lemma grahamK23_pair_reaches_in_left_cut_eq :
-- imply
  grahamK23ReachWithin {0, 2} 0 2 := by
-- proof
  apply StatMech.FrontierA.grahamK23_pair_reaches_in_left_cut

/--
[grahamK23_pair_reaches_in_right_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean)
-/
@[path]
private lemma grahamK23_pair_reaches_in_right_cut_eq :
-- imply
  grahamK23ReachWithin {1, 2} 2 1 := by
-- proof
  apply StatMech.FrontierA.grahamK23_pair_reaches_in_right_cut

/--
[grahamK23_not_rawCutFourFunctions_of_exactSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean)
-/
@[path]
private lemma grahamK23_not_rawCutFourFunctions_of_exactSupport_eq
-- given
  (mu f g : Finset (Fin 5) -> Real)
  (hmu : ∀ S, 0 <= mu S)
  (hsupport : ∀ S, 0 < mu S <-> GrahamK23RootCutSupported S)
  (hf : 0 < f {0, 2})
  (hg : 0 < g {1, 2}) :
-- imply
  ¬ ∀ A B : Finset (Fin 5), (mu A * f A) * (mu B * g B) <= mu (A ∩ B) * (mu (A ∪ B) * (f (A ∪ B) * g (A ∪ B))) := by
-- proof
  apply StatMech.FrontierA.grahamK23_not_rawCutFourFunctions_of_exactSupport mu f g hmu hsupport hf hg


-- created on 2026-10-23
