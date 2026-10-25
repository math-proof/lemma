/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part3
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising

noncomputable section

@[simp] theorem surfaceHomologyCharacter_zero {g : Nat}
    (lambda : SurfaceSpinStructure g) :
    surfaceHomologyCharacter lambda 0 = 1 := by
  simp [surfaceHomologyCharacter, surfaceSpinLinearParity]

theorem surfaceHomologyCharacter_add {g : Nat}
    (lambda : SurfaceSpinStructure g) (h k : SurfaceHomology g) :
    surfaceHomologyCharacter lambda (h + k) =
      surfaceHomologyCharacter lambda h * surfaceHomologyCharacter lambda k := by
  unfold surfaceHomologyCharacter
  rw [surfaceSpinLinearParity_add, surfaceParitySign_add]
  push_cast
  rfl

theorem surfaceHomologyCharacter_finset_sum {g : Nat}
    {ι : Type*} [DecidableEq ι] (lambda : SurfaceSpinStructure g)
    (S : Finset ι) (f : ι → SurfaceHomology g) :
    surfaceHomologyCharacter lambda (∑ i ∈ S, f i) =
      ∏ i ∈ S, surfaceHomologyCharacter lambda (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        surfaceHomologyCharacter_add, ih]

end
end StatMech.FrontierA
