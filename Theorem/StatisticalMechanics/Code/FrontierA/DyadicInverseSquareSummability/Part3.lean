/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/DyadicInverseSquareSummability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Def.StatisticalMechanics.Code.FrontierA.DyadicInverseSquareSummability.Part2
open Filter Finset Set Topology


namespace StatMech.FrontierA

noncomputable section

theorem finite_dyadicUpperFiber
    {Q : Type*} (size : Q → Real)
    (hfinite : ∀ R : Real, Set.Finite {q | size q ≤ R}) (n : Nat) :
    Finite (DyadicUpperFiber size n) := by
  let target : Set Q := {q | size q ≤ (2 : Real) ^ n}
  have htarget : target.Finite := hfinite ((2 : Real) ^ n)
  letI : Fintype target := htarget.fintype
  let f : DyadicUpperFiber size n → target := fun q =>
    ⟨q.1, by
      change size q.1 ≤ (2 : Real) ^ n
      simpa [q.2] using size_le_two_pow_dyadicUpperLevel size q.1⟩
  exact Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    change a.1 = b.1
    exact congrArg (fun x : target => x.1) h)

end
end StatMech.FrontierA
