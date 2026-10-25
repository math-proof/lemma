/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Order.DirectedInverseSystem
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib
import Structure.v1.Atlas.ArithmeticGeometry.code.PadicNumbers


namespace InverseLimit

namespace NatInverseSystem

variable (S : NatInverseSystem)

/-- The inverse limit of a `NatInverseSystem` $S$: coherent sequences $(a_n)$ with
$a_n \in S_n$ and $S.\mathrm{map}\,n\,(a_{n+1}) = a_n$. -/
def InverseLimit : Type _ :=
  { a : ∀ n, S.obj n // ∀ n, S.map n (a (n + 1)) = a n }

/-- Canonical projection $\mathrm{proj}_n : \mathrm{InverseLimit}\,S \to S_n$. -/
def proj (n : ℕ) (a : S.InverseLimit) : S.obj n :=
  a.val n

/-- Universal property (lift): a compatible family `g n : X → S.obj n` factors through the
inverse limit. -/
def lift {X : Type*} (g : ∀ n, X → S.obj n)
    (hg : ∀ n x, S.map n (g (n + 1) x) = g n x) : X → S.InverseLimit :=
  fun x => ⟨fun n => g n x, fun n => hg n x⟩

end NatInverseSystem
end InverseLimit
