/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Janson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Choose
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Janson

@[expose] public section

set_option maxHeartbeats 800000

open Filter Real
open scoped Topology


noncomputable section

namespace Janson

/-- Decidability of the dependency relation. -/
instance (J : JansonSetup) (i j : Fin J.k) : Decidable (J.dep i j) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Janson
end
