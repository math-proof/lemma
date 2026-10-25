/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionThermodynamic.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDisorderGluing.Part2
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.flexible false
set_option linter.style.multiGoal false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


section DisjointBlocks

variable {P₁ P₂ V₁ V₂ : Type*}
  [Fintype P₁] [DecidableEq P₁] [Fintype P₂] [DecidableEq P₂]
  [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]


def multibondSumEnds (ends₁ : P₁ → V₁ × V₁) (ends₂ : P₂ → V₂ × V₂) :
    P₁ ⊕ P₂ → (V₁ ⊕ V₂) × (V₁ ⊕ V₂)
  | .inl p => (.inl (ends₁ p).1, .inl (ends₁ p).2)
  | .inr p => (.inr (ends₂ p).1, .inr (ends₂ p).2)


def multibondSumCoupling (J₁ : P₁ → Real) (J₂ : P₂ → Real) :
    P₁ ⊕ P₂ → Real :=
  Sum.elim J₁ J₂


def multibondSumSheet (D₁ : Finset P₁) (D₂ : Finset P₂) : Finset (P₁ ⊕ P₂) :=
  D₁.disjSum D₂


end DisjointBlocks
end
end StatMech.FrontierA
