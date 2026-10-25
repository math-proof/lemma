/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralFinite
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E D : Type*} [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D]
  {S : E → Type*} [∀ e, Fintype (S e)]


noncomputable def piCylinderMin (f : (∀ e, S e) → ℝ) (K : Set E)
    (x : ∀ e, S e) : ℝ :=
  (piAgreementFiber K x).inf' (piAgreementFiber_nonempty K x) f


noncomputable def piFunctionalDisjointMaxAt
    (f g : (∀ e, S e) → ℝ) (x y : ∀ e, S e) : ℝ :=
  (disjointCoordinatePairs E).sup' (disjointCoordinatePairs_nonempty (E := E))
    fun pair => piCylinderMin f pair.1 x * piCylinderMin g pair.2 y


noncomputable def piFunctionalDisjointMax
    (f g : (∀ e, S e) → ℝ) (x : ∀ e, S e) : ℝ :=
  piFunctionalDisjointMaxAt f g x x


def decodeBlockConfig (decode : ∀ e, (D → Bool) → S e)
    (omega : ConfigSpace (E × D)) : ∀ e, S e :=
  fun e => decode e (fun d => omega (e, d))


def wholeBlocks (K : Set E) : Set (E × D) :=
  {z | z.1 ∈ K}

end StatMech.FrontierA
