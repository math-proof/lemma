/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangZeroFree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part15
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.LogDeriv
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def leeYangComplexFieldPartition (beta : ℝ) (h : ℂ) : ℂ :=
  ∑ s : ConfigSpace V, Complex.exp
    ((beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e) +
      (beta : ℂ) * h * (∑ v : V, spin s v))


end StatMech.FrontierA
