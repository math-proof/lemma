/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/AlgorithmicLLL.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.AlgorithmicLLL


namespace AlgorithmicLLL

variable {Clause : Type*} {State : Type*}

variable {sys : FixSystem Clause State}

/-- `IsValidOuterLoop sys cs s` says that the list of clauses `cs` is a valid execution
trace of the outer loop of Moser's algorithm starting from state `s`: each successive
clause is unsatisfied at the moment it is visited and then fixed. -/
def IsValidOuterLoop (sys : FixSystem Clause State) :
    List Clause → State → Prop
  | [], _ => True
  | c :: cs, s => ¬sys.satisfied c s ∧ IsValidOuterLoop sys cs (sys.fix c s)

end AlgorithmicLLL
