/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexGenuineStripPhaseObstruction


namespace StatMech.Universality

open Complex Set

open scoped BigOperators


structure HexMirrorBoundaryPair
    {V : Type*} [DecidableEq V]
    (D : HexDomain V) (heading : V → Fin 3 → ℤ) where
  neg : Finset (HexIncidence V)
  pos : Finset (HexIncidence V)
  disjoint : Disjoint neg pos
  headNeg : ℤ
  headPos : ℤ
  hHeadNeg : ∀ e ∈ neg, heading e.vtx e.edge = headNeg
  hHeadPos : ∀ e ∈ pos, heading e.vtx e.edge = headPos
  angle : ℝ
  mass : ℝ
  phaseNeg :
    (∑ e ∈ neg, D.obs (D.mid e.vtx e.edge)) =
      Complex.exp ((hexPhase_sideTilt headNeg : ℝ) * Complex.I) *
        (Complex.exp ((-angle : ℝ) * Complex.I) * (mass : ℂ))
  phasePos :
    (∑ e ∈ pos, D.obs (D.mid e.vtx e.edge)) =
      Complex.exp ((hexPhase_sideTilt headPos : ℝ) * Complex.I) *
        (Complex.exp ((angle : ℝ) * Complex.I) * (mass : ℂ))

end StatMech.Universality
