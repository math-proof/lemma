/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

def fixedWordProduct {E R : Type*} [CommMonoid R] (A : Matrix E E R)
    {k : ℕ} (p : Fin (k + 1) → E) : R :=
  ∏ i : Fin k, A (p i.castSucc) (p i.succ)

def pathCastEquiv (E : Type*) {m n : ℕ} (h : m = n) :
    (Fin m → E) ≃ (Fin n → E) :=
  Equiv.arrowCongr (finCongr h) (Equiv.refl E)

end StatMech.FrontierB
