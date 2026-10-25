/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangHarris.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
open MeasureTheory Set SimpleGraph
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


def zfe_primalEmb (p : Site 2) : Site 2 := ![2 * p 0, 2 * p 1]


def zfe_primalMid (p q : Site 2) : Site 2 := ![p 0 + q 0, p 1 + q 1]


def zfe_faceEmb (f : Site 2) : Site 2 := ![2 * f 0 + 1, 2 * f 1 + 1]


def zfe_faceMid (f g : Site 2) : Site 2 :=
  ![f 0 + g 0 + 1, f 1 + g 1 + 1]

end StatMech.TwoDim
