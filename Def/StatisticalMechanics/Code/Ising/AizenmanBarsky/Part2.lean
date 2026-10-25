/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def cov2 (β h : ℝ) (x y : V) : ℝ :=
  isingExpectation G β h (fun s => spin s x * spin s y)
    - isingExpectation G β h (fun s => spin s x) * isingExpectation G β h (fun s => spin s y)


noncomputable def onePt (β h : ℝ) (x : V) : ℝ := isingExpectation G β h (fun s => spin s x)


noncomputable def cov3sym (β h : ℝ) (o : V) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun x y =>
    isingExpectation G β h (fun s => spin s o * (spin s x * spin s y))
      - isingExpectation G β h (fun s => spin s o)
          * isingExpectation G β h (fun s => spin s x * spin s y), by
    intro a b
    have h1 : (fun s : ConfigSpace V => spin s o * (spin s a * spin s b))
        = (fun s => spin s o * (spin s b * spin s a)) := by funext s; ring
    have h2 : (fun s : ConfigSpace V => spin s a * spin s b)
        = (fun s => spin s b * spin s a) := by funext s; ring
    simp only []; rw [h1, h2]⟩ e

end Ising
end StatMech
