/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Poincare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace Poincare

open DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]


def fullTree (φ : ConfigSpace E → Bool) : List E → DecisionTree E
  | [] => .leaf (φ (fun _ => false))
  | (e :: l) =>
      .node e (fullTree (fun ω => φ (setOpen e ω)) l)
              (fullTree (fun ω => φ (setClosed e ω)) l)


def InsensOutside (φ : ConfigSpace E → Bool) (l : List E) : Prop :=
  ∀ ω ω', (∀ e ∈ l, ω e = ω' e) → φ ω = φ ω'

end Poincare
end OSSS
end StatMech
