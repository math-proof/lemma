/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeSum
import Theorem.StatisticalMechanics.Code.Sharpness.GHSConcavity
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part2
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option maxHeartbeats 2400000


namespace StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ghsiTWeight (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q a : ConfigSpace V) : ℝ :=
  Real.exp
    ((∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q),
        (2 * K e) * bond a e) +
      ∑ v ∈ ghsLAgreeFinset q, (2 * hf v) * spin a v)


noncomputable def ghsiUWeight (K : Sym2 V → ℝ) (q a : ConfigSpace V) : ℝ :=
  Real.exp
    (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ,
      (2 * K e) * bond a e)


end StatMech.Ising
