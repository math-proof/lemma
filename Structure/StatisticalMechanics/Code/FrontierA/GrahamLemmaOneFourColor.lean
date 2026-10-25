/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamLemmaOneFourColor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
open Finset SimpleGraph
open scoped symmDiff
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


structure GrahamFourColoring (ι : Type*) where
  color1 : Finset ι
  color2 : Finset ι
  color3 : Finset ι
deriving DecidableEq, Fintype


end StatMech.FrontierA
