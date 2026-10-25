/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.STT.Part4
import Theorem.StatisticalMechanics.Code.Universality.STTTransport.Part3
import Structure.StatisticalMechanics.Code.Universality.BXPTransfer
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


theorem bxp_square_of_triangular
    {μsq μtri : Measure (ConfigSpace (Sym2 (Site 2)))} {ρsq ρtri : ℝ}
    (hdata : CrossingTransportData μsq μtri ρsq ρtri)
    (htri : BoxCrossingProperty μtri ρtri) :
    BoxCrossingProperty μsq ρsq := by
  obtain ⟨_, n0, hpos⟩ := htri
  exact bxp_transfer_core μsq μtri ρsq ρtri n0 n0 hdata.one_lt_ρsq hpos
    (hdata.sqDominatedByTri n0)


theorem bxp_triangular_of_square
    {μsq μtri : Measure (ConfigSpace (Sym2 (Site 2)))} {ρsq ρtri : ℝ}
    (hdata : CrossingTransportData μsq μtri ρsq ρtri)
    (hsq : BoxCrossingProperty μsq ρsq) :
    BoxCrossingProperty μtri ρtri := by
  obtain ⟨_, n0, hpos⟩ := hsq
  exact bxp_transfer_core μtri μsq ρtri ρsq n0 n0 hdata.one_lt_ρtri hpos
    (hdata.triDominatedBySq n0)


theorem bxp_square_iff_triangular
    {μsq μtri : Measure (ConfigSpace (Sym2 (Site 2)))} {ρsq ρtri : ℝ}
    {p0 p1 p2 : ℝ} (hcrit : IsCriticalTri p0 p1 p2)
    (hdata : CrossingTransportData μsq μtri ρsq ρtri) :
    BoxCrossingProperty μsq ρsq ↔ BoxCrossingProperty μtri ρtri := by
  
  
  
  
  
  have _hconn := starTriangle_connectivity p0 p1 p2 hcrit
  exact ⟨bxp_triangular_of_square hdata, bxp_square_of_triangular hdata⟩

end Universality
end StatMech
