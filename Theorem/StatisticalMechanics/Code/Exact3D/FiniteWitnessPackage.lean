/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part15
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteSupportCertificateConsequences
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
import Structure.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace RGCertificate

theorem FiniteChecks.valid_of_bridge {ι : Type*} {M : CriticalModel ι}
    {C : RGCertificate M} {correlationLength : ℝ → ℝ}
    (h : C.FiniteChecks)
    (hbridge : C.RGToExponentBridge correlationLength) :
    C.Valid correlationLength where
  finiteCaseChecks := h.finiteCaseChecks
  tailBounds := h.tailBounds
  fixedPointEnclosure := h.fixedPointEnclosure
  linearizationEnclosure := h.linearizationEnclosure
  hyperbolicSplitting := h.hyperbolicSplitting
  orbitEntry := h.orbitEntry
  bridge := hbridge


theorem FiniteChecks.hasCriticalNu_of_bridge {ι : Type*}
    {M : CriticalModel ι} {C : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (h : C.FiniteChecks)
    (hbridge : C.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength C.predictedExponent :=
  (h.valid_of_bridge hbridge).hasCriticalNu


theorem FiniteChecks.rgToExponentBridge_of_hasCriticalNu {ι : Type*}
    {M : CriticalModel ι} {C : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (_h : C.FiniteChecks)
    (hν : HasCriticalNu M correlationLength C.predictedExponent) :
    C.RGToExponentBridge correlationLength :=
  C.bridge_of_hasCriticalNu correlationLength hν


theorem FiniteChecks.valid_of_hasCriticalNu {ι : Type*} {M : CriticalModel ι}
    {C : RGCertificate M} {correlationLength : ℝ → ℝ}
    (h : C.FiniteChecks)
    (hν : HasCriticalNu M correlationLength C.predictedExponent) :
    C.Valid correlationLength :=
  h.valid_of_bridge (h.rgToExponentBridge_of_hasCriticalNu hν)

end RGCertificate
end Exact3D
end StatMech
