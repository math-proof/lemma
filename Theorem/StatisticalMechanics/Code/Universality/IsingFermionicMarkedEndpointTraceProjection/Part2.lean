/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointTraceProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryProjectionSampling.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointInputAssembly
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPolynomialEndpointConvergence.Part2
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointTraceProjection


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem LocalBoundaryTraceProjection.error_le
    {Phi : Complex -> Complex} {S : Set Complex} {L : NNReal}
    {sample : Complex} {value mesh : Real}
    (P : LocalBoundaryTraceProjection Phi S L sample value mesh)
    (hPhi : LipschitzOnWith L (fun z => (Phi z).im) S) :
    |value - (Phi sample).im| <= L * mesh :=
  boundaryTrace_abs_sub_le_of_lipschitzOn Phi S L hPhi
    sample P.boundaryPoint value mesh P.sample_mem P.boundary_mem
    P.trace P.dist_le_mesh


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
