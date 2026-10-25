/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector
open Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

namespace shb_DynamicEdgeExploration

variable {D E : Type*} [DecidableEq E]


def determinedAt (X : shb_DynamicEdgeExploration D E) (d : D) (e : E) : List E :=
  (X.edgeOrder d).takeWhile (fun f => f ≠ e) ++ [e]


def residual (X : shb_DynamicEdgeExploration D E) : D → List E → D
  | d, [] => d
  | d, e :: es => residual X (X.advance d e) es


def determinedTrace (X : shb_DynamicEdgeExploration D E) : D → List E → List E
  | _, [] => []
  | d, e :: es => X.determinedAt d e ++ X.determinedTrace (X.advance d e) es


def Selects (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) : D → List E → Prop
  | _, [] => True
  | d, e :: es =>
      X.firstAdmissible admissible d = some e ∧
        X.Selects admissible (X.advance d e) es

end shb_DynamicEdgeExploration
end StatMech.Sharpness
