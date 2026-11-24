module
public import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
public import Theorem.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition.Part3
public import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
public import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeSum
public import Theorem.StatisticalMechanics.Code.Sharpness.GHSConcavity
public import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part5
open scoped BigOperators symmDiff
open Finset SimpleGraph Set
set_option maxHeartbeats 2400000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ghsiDisagreementCorr (K : Sym2 V → ℝ)
    (o x : V) (A : Finset V) : ℝ :=
  if o ∈ A ∨ x ∈ A then 0
  else ghsvp_vertexCorr G.edgeFinset (fun e => 2 * K e) Aᶜ {o, x}


noncomputable def ghsiAgreementMag (K : Sym2 V → ℝ) (hf : V → ℝ)
    (y : V) (A : Finset V) : ℝ :=
  if y ∈ A then
    ghsvp_vertexCorrField G.edgeFinset (fun e => 2 * K e) (fun x => 2 * hf x) A {y}
  else 0

end StatMech.Ising
