/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw.Part3
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
import Theorem.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part4
import Theorem.StatisticalMechanics.Code.OSSS.PredictableTreeQuery
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part7
open scoped BigOperators
open MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace OSSS

namespace AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


def fixedListOrder : (l : List E) → l.Nodup → CausalOrder l.toFinset
  | [], _ => .done
  | e :: l, h => by
      have he : e ∉ l := (List.nodup_cons.mp h).1
      have ht : l.Nodup := (List.nodup_cons.mp h).2
      have hem : e ∈ (e :: l).toFinset := by simp
      have herase : (e :: l).toFinset.erase e = l.toFinset := by
        ext z
        simp [he]
      have child : CausalOrder ((e :: l).toFinset.erase e) :=
        herase.symm ▸ fixedListOrder l ht
      exact CausalOrder.node e hem true child child


noncomputable def fixedOrder (R : Finset E) : CausalOrder R :=
  R.toList_toFinset ▸ fixedListOrder R.toList R.nodup_toList

def TripleOrder.beforeOfCausal : {R : Finset E} → CausalOrder R → TripleOrder R
  | _, .done => .done
  | _, .node e he _ closed opened =>
      .node e he .before (TripleOrder.beforeOfCausal closed)
        (TripleOrder.beforeOfCausal opened)


noncomputable def extendDecisionTreeTriple :
    Option ℕ → DecisionTree E → ConfigSpace E → (R : Finset E) → TripleOrder R
  | _, .leaf _, _, R => TripleOrder.beforeOfCausal (fixedOrder R)
  | phase, .node e opened closed, known, R =>
      if he : e ∈ R then
        match phase with
        | some 0 => .node e he .flip
            (extendDecisionTreeTriple none closed (Function.update known e false) (R.erase e))
            (extendDecisionTreeTriple none opened (Function.update known e true) (R.erase e))
        | some (t + 1) => .node e he .before
            (extendDecisionTreeTriple (some t) closed (Function.update known e false) (R.erase e))
            (extendDecisionTreeTriple (some t) opened (Function.update known e true) (R.erase e))
        | none => .node e he .after
            (extendDecisionTreeTriple none closed (Function.update known e false) (R.erase e))
            (extendDecisionTreeTriple none opened (Function.update known e true) (R.erase e))
      else if known e then extendDecisionTreeTriple phase opened known R
      else extendDecisionTreeTriple phase closed known R

end AdaptiveCausalKernel
end OSSS
end StatMech
