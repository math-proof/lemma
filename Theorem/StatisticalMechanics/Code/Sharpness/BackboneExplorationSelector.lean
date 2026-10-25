/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector
open Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

namespace shb_DynamicEdgeExploration

variable {D E : Type*} [DecidableEq E]


theorem firstAdmissible_mem (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) (e : E)
    (h : X.firstAdmissible admissible d = some e) :
    e ∈ X.edgeOrder d :=
  List.mem_of_find?_eq_some h


theorem firstAdmissible_isAdmissible (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) (e : E)
    (h : X.firstAdmissible admissible d = some e) :
    admissible d e = true :=
  List.find?_some h


end shb_DynamicEdgeExploration
end StatMech.Sharpness
