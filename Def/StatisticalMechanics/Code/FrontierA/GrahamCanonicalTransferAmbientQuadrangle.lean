/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageExchange.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def LeftSourcePattern (ends : I -> Sym2 W) (m : Finset I)
    (A B : Finset W) (c : ↑m -> Fin 4) : Prop :=
  sources ends (colorClass m c 0) = A ∧
    sources ends (colorClass m c 1) = ∅ ∧
    sources ends (colorClass m c 2) = B ∧
    sources ends (colorClass m c 3) = ∅


def leftSourceMaskFiber (ends : I -> Sym2 W) (m : Finset I)
    (j k l zero : W) (p : Finset I × Finset I) :=
  {c : ↑m -> Fin 4 //
    LeftSourcePattern ends m {j, k} {k, l} c ∧
      fourColorMaskProfile m c = p}

end StatMech.GrahamGHS.FourColor
