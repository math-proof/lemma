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
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive
open MeasureTheory Set SimpleGraph
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


def zfe_primalSubdiv {p q : Site 2} :
    (hypercubicLattice 2).Walk p q →
      (hypercubicLattice 2).Walk (zfe_primalEmb p) (zfe_primalEmb q)
  | .nil => .nil
  | .cons h w => .cons (zfe_primalEmb_mid_adj h)
      (.cons (zfe_primalMid_emb_adj h) (zfe_primalSubdiv w))


def zfe_faceSubdiv {f g : Site 2} :
    (hypercubicLattice 2).Walk f g →
      (hypercubicLattice 2).Walk (zfe_faceEmb f) (zfe_faceEmb g)
  | .nil => .nil
  | .cons h w => .cons (zfe_faceEmb_mid_adj h)
      (.cons (zfe_faceMid_emb_adj h) (zfe_faceSubdiv w))

end StatMech.TwoDim
