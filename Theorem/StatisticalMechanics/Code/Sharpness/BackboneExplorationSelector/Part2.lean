/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector.Part2
open Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

namespace shb_DynamicEdgeExploration

variable {D E : Type*} [DecidableEq E]


@[simp] theorem residual_nil (X : shb_DynamicEdgeExploration D E) (d : D) :
    X.residual d [] = d := rfl

@[simp] theorem residual_cons (X : shb_DynamicEdgeExploration D E)
    (d : D) (e : E) (es : List E) :
    X.residual d (e :: es) = X.residual (X.advance d e) es := rfl


theorem residual_append (X : shb_DynamicEdgeExploration D E)
    (d : D) (p q : List E) :
    X.residual d (p ++ q) = X.residual (X.residual d p) q := by
  induction p generalizing d with
  | nil => rfl
  | cons e p ih =>
      simp only [List.cons_append, residual_cons]
      exact ih (X.advance d e)

@[simp] theorem determinedTrace_nil (X : shb_DynamicEdgeExploration D E) (d : D) :
    X.determinedTrace d [] = [] := rfl

@[simp] theorem determinedTrace_cons (X : shb_DynamicEdgeExploration D E)
    (d : D) (e : E) (es : List E) :
    X.determinedTrace d (e :: es) =
      X.determinedAt d e ++ X.determinedTrace (X.advance d e) es := rfl


theorem determinedTrace_append (X : shb_DynamicEdgeExploration D E)
    (d : D) (p q : List E) :
    X.determinedTrace d (p ++ q) =
      X.determinedTrace d p ++ X.determinedTrace (X.residual d p) q := by
  induction p generalizing d with
  | nil => rfl
  | cons e p ih =>
      simp only [List.cons_append, determinedTrace_cons, residual_cons]
      rw [ih]
      exact (List.append_assoc _ _ _).symm

@[simp] theorem selects_nil (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) :
    X.Selects admissible d [] := trivial

@[simp] theorem selects_cons (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) (e : E) (es : List E) :
    X.Selects admissible d (e :: es) ↔
      X.firstAdmissible admissible d = some e ∧
        X.Selects admissible (X.advance d e) es := Iff.rfl


theorem selects_append_iff (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) (p q : List E) :
    X.Selects admissible d (p ++ q) ↔
      X.Selects admissible d p ∧
        X.Selects admissible (X.residual d p) q := by
  induction p generalizing d with
  | nil => simp
  | cons e p ih =>
      simp only [List.cons_append, selects_cons, residual_cons, ih]
      tauto

end shb_DynamicEdgeExploration
end StatMech.Sharpness
