/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedEdgeLumping.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
open Finset


namespace StatMech.FK

noncomputable section

variable {E A : Type*} [Fintype E] [DecidableEq E]
  [Fintype A] [DecidableEq A]


def indexedBernoulliWeight (p : Real) (eta : E → Bool) : Real :=
  ∏ e, if eta e then p else 1 - p


def indexedBundleSupport (f : E → A) (eta : E → Bool) : A → Bool :=
  fun a => decide (∃ e, f e = a ∧ eta e = true)


def indexedBundle (f : E → A) (a : A) : Finset E :=
  Finset.univ.filter (fun e => f e = a)


def indexedEffectiveParam (f : E → A) (p : Real) (a : A) : Real :=
  1 - (1 - p) ^ (indexedBundle f a).card

def indexedFiberOr (f : E → A) (a : A)
    (eta : {e : E // f e = a} → Bool) : Bool :=
  decide (∃ e, eta e = true)

def indexedFiberWeight (p : Real) {f : E → A} {a : A}
    (eta : {e : E // f e = a} → Bool) : Real :=
  ∏ e, if eta e then p else 1 - p

end
end StatMech.FK
