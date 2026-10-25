/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_lotempexpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
open scoped BigOperators
open Finset


namespace StatMech.Walls

open StatMech.Ising


variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def kwdCutEdges (s : ConfigSpace V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => bond s e = -1)

end StatMech.Walls
