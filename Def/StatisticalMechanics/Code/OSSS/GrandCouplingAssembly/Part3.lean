/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.GrandCoupling.Part3
import Theorem.StatisticalMechanics.Code.OSSS.LindebergTree.Part6
import Theorem.StatisticalMechanics.Code.OSSS.GrandCouplingAssembly.Part3
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace GrandCouplingAssembly

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling StatMech.Probability

variable {E : Type*} [Fintype E] [DecidableEq E]


def projInl (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) : Fin n → ℝ := fun i => w (Sum.inl i)


noncomputable def combine (n : ℕ) :
    ((Fin n → ℝ) × (Fin n → ℝ)) ≃ᵐ (Fin n ⊕ Fin n → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ)).symm

end GrandCouplingAssembly
end OSSS
end StatMech
