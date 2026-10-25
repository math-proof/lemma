/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.FSMartingale.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]


noncomputable def mxd_maxE [Nonempty ι] (S : Finset ι) : ι :=
  if h : S.Nonempty then S.max' h else Classical.arbitrary ι


end StatMech.Probability
