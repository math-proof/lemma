/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCylinderTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferObservable
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Def.StatisticalMechanics.Code.Ising.IsingCylinderTransfer.Part3
open Finset Matrix Filter Topology
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]


theorem isingCylinderEndpointMean_tendsto
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (leftBoundary rightBoundary : ConfigSpace W -> Real)
    (obs : ConfigSpace W -> Real) :
    exists lam : Real, 0 < lam ∧
      exists u : EuclideanSpace Real (ConfigSpace W),
        (forall s, 0 < u s) ∧ norm u = 1 ∧
        isingCylinderTransfer E J h Jvertical *ᵥ (fun s => u s) =
          lam • (fun s => u s) ∧
        Tendsto
          (isingCylinderEndpointMean E J h Jvertical
            leftBoundary rightBoundary obs)
          atTop
          (nhds ((∑ s,
              isingCylinderBoundaryVector E J h rightBoundary s *
                obs s * u s) /
            ∑ s, isingCylinderBoundaryVector E J h rightBoundary s * u s)) := by
  simpa [isingCylinderEndpointMean] using
    positiveTransfer_endpointObservable_tendsto
      (isingCylinderTransfer E J h Jvertical)
      (isingCylinderTransfer_isHermitian E J h Jvertical)
      (isingCylinderTransfer_pos E J h Jvertical)
      (isingCylinderBoundaryVector E J h leftBoundary)
      (isingCylinderBoundaryVector E J h rightBoundary)
      (isingCylinderBoundaryVector_pos E J h leftBoundary)
      (isingCylinderBoundaryVector_pos E J h rightBoundary) obs


theorem isingCylinderEndpointSpin_tendsto
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (leftBoundary rightBoundary : ConfigSpace W -> Real) (x : W) :
    exists m : Real,
      Tendsto
        (isingCylinderEndpointMean E J h Jvertical
          leftBoundary rightBoundary (fun s => spin s x))
        atTop (nhds m) := by
  obtain ⟨lam, hlam, u, hupos, hunorm, hueig, hlim⟩ :=
    isingCylinderEndpointMean_tendsto E J h Jvertical
      leftBoundary rightBoundary (fun s => spin s x)
  exact ⟨(∑ s, isingCylinderBoundaryVector E J h rightBoundary s *
      spin s x * u s) /
    ∑ s, isingCylinderBoundaryVector E J h rightBoundary s * u s, hlim⟩


theorem isingCylinder_twoBoundaryEndpoint_common
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (leftBoundaryA leftBoundaryB rightBoundary : ConfigSpace W -> Real)
    (obs : ConfigSpace W -> Real) :
    exists m : Real,
      Tendsto
        (isingCylinderEndpointMean E J h Jvertical
          leftBoundaryA rightBoundary obs) atTop (nhds m) ∧
      Tendsto
        (isingCylinderEndpointMean E J h Jvertical
          leftBoundaryB rightBoundary obs) atTop (nhds m) := by
  simpa [isingCylinderEndpointMean] using
    positiveTransfer_twoBoundary_endpointObservable_common
      (isingCylinderTransfer E J h Jvertical)
      (isingCylinderTransfer_isHermitian E J h Jvertical)
      (isingCylinderTransfer_pos E J h Jvertical)
      (isingCylinderBoundaryVector E J h leftBoundaryA)
      (isingCylinderBoundaryVector E J h leftBoundaryB)
      (isingCylinderBoundaryVector E J h rightBoundary)
      (isingCylinderBoundaryVector_pos E J h leftBoundaryA)
      (isingCylinderBoundaryVector_pos E J h leftBoundaryB)
      (isingCylinderBoundaryVector_pos E J h rightBoundary) obs


theorem isingCylinder_twoBoundarySpin_common
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (leftBoundaryA leftBoundaryB rightBoundary : ConfigSpace W -> Real)
    (x : W) :
    exists m : Real,
      Tendsto
        (isingCylinderEndpointMean E J h Jvertical
          leftBoundaryA rightBoundary (fun s => spin s x))
        atTop (nhds m) ∧
      Tendsto
        (isingCylinderEndpointMean E J h Jvertical
          leftBoundaryB rightBoundary (fun s => spin s x))
        atTop (nhds m) :=
  isingCylinder_twoBoundaryEndpoint_common E J h Jvertical
    leftBoundaryA leftBoundaryB rightBoundary (fun s => spin s x)


theorem isingCylinderPartition_log_div_tendsto
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (leftBoundary rightBoundary : ConfigSpace W -> Real) :
    exists lam : Real, 0 < lam ∧
      Tendsto (fun n : Nat =>
        Real.log (isingCylinderPartition E J h Jvertical
          leftBoundary rightBoundary n) / (n : Real))
        atTop (nhds (Real.log lam)) := by
  simpa [isingCylinderPartition] using
    positiveTransfer_log_dotProduct_div_tendsto
      (isingCylinderTransfer E J h Jvertical)
      (isingCylinderTransfer_isHermitian E J h Jvertical)
      (isingCylinderTransfer_pos E J h Jvertical)
      (isingCylinderBoundaryVector E J h leftBoundary)
      (isingCylinderBoundaryVector E J h rightBoundary)
      (isingCylinderBoundaryVector_pos E J h leftBoundary)
      (isingCylinderBoundaryVector_pos E J h rightBoundary)

end
end StatMech.Ising
