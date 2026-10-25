/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectedMatchingCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterMatchingCutCurrent.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W I : Type*} [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]


structure LPReflectedMatchingCut
    (G : SimpleGraph W) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) where
  reflect : Equiv.Perm W
  involutive : Function.Involutive reflect
  reflect_left : forall i, reflect (left i) = right i
  reflect_right : forall i, reflect (right i) = left i
  reflect_g0 : reflect g0 = g1
  reflect_g1 : reflect g1 = g0
  adj_iff : forall x y, G.Adj (reflect x) (reflect y) <-> G.Adj x y
  coupling : forall e, J (Sym2.map reflect e) = J e


end
end StatMech.Ising
