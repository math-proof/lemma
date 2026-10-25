/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferQuadrangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferPairExpansion.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

noncomputable def canonicalMiddleTransferDifference
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b : ↑m -> Fin 4) : Finset I :=
  canonicalMiddleTransfer ends m a k zero ∆
    canonicalMiddleTransfer ends m b k zero

noncomputable def canonicalOuterTransferDifference
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b : ↑m -> Fin 4) : Finset I :=
  canonicalOuterTransfer ends m a k zero ∆
    canonicalOuterTransfer ends m b k zero


noncomputable def canonicalQuadrangleCompletion
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b c : ↑m -> Fin 4) : ↑m -> Fin 4 :=
  balancedSwap m
    (canonicalMiddleTransferDifference ends m k zero a b)
    (canonicalOuterTransferDifference ends m k zero a b) c


end StatMech.GrahamGHS.FourColor
