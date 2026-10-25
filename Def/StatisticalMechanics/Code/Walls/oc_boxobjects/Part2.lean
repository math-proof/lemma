/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RussoDerivative.Part5
import Theorem.StatisticalMechanics.Code.FK.FKQ2Sharp
import Theorem.StatisticalMechanics.Code.FK.Comparison
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Structure.StatisticalMechanics.Code.Walls.oc_boxobjects
open scoped BigOperators
open Finset Set
open scoped Classical

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace Walls

open StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def oc_boxFamily (Gf : ℕ → SimpleGraph V) [∀ n, DecidableRel (Gf n).Adj]
    (Af : ℕ → Set (ConfigSpace (Sym2 V))) (hAf : ∀ n, IsIncreasing (Af n)) :
    oc_BoxFamily where
  theta n β := oc_theta Gf Af n β
  S n β := oc_S Gf Af n β
  thetaDeriv n β :=
    (∑ e ∈ (Gf n).edgeFinset,
        fkCov (Gf n) β 2 ((Af n).indicator (fun _ => (1 : ℝ))) (coord e))
      / (β * (1 - β))
  theta_nonneg := fun {_β} hβ hβ1 n => oc_theta_nonneg Gf Af hβ hβ1 n
  theta_le_one := fun {_β} hβ hβ1 n => oc_theta_le_one Gf Af hβ hβ1 n
  hasDerivAt_theta := fun {_β} hβ hβ1 n => oc_hasDerivAt_theta Gf Af hβ hβ1 n
  theta_mono := fun n {_β₁ _β₂} hβ₁ hβ₂1 hle => oc_theta_mono Gf Af hAf n hβ₁ hβ₂1 hle
  S_succ n β := oc_S_succ Gf Af n β
  S_zero β := oc_S_zero Gf Af β


end Walls
end StatMech
