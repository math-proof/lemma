/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryPhases


namespace StatMech.Universality

open Complex

open scoped BigOperators


variable {V : Type*} [DecidableEq V]
  {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}


structure HexPhaseData (D : HexDomain V) (P : D.InteriorPairing) (R : HexRegion) where
  
  heading : V → Fin 3 → ℤ
  
  hgeom : ∀ v j, D.mid v j - D.pos v = (1 / 2 : ℂ) * hexUnit (heading v j)
  
  headA : ℤ
  
  headL : ℤ
  
  headTp : ℤ
  
  headTm : ℤ
  
  headU : ℤ
  
  hHeadA : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 0),
    heading e.vtx e.edge = headA
  
  hHeadL : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 1),
    heading e.vtx e.edge = headL
  
  hHeadTp : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 2),
    heading e.vtx e.edge = headTp
  
  hHeadTm : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 3),
    heading e.vtx e.edge = headTm
  
  hHeadU : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 4),
    heading e.vtx e.edge = headU
  
  lam : ℝ
  
  taup : ℝ
  
  taum : ℝ
  
  ups : ℝ
  
  Fa : ℝ
  

  phaseA : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 0),
        D.obs (D.mid e.vtx e.edge))
      = 2 * Complex.exp ((hexPhase_sideTilt headA : ℝ) * Complex.I) * (((-1 : ℝ) * Fa : ℝ) : ℂ)
  

  phaseL : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 1),
        D.obs (D.mid e.vtx e.edge))
      = 2 * Complex.exp ((hexPhase_sideTilt headL : ℝ) * Complex.I) * ((hexBdryCl * lam : ℝ) : ℂ)
  

  phaseTp : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 2),
        D.obs (D.mid e.vtx e.edge))
      = 2 * Complex.exp ((hexPhase_sideTilt headTp : ℝ) * Complex.I) * ((hexBdryCt * taup : ℝ) : ℂ)
  

  phaseTm : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 3),
        D.obs (D.mid e.vtx e.edge))
      = 2 * Complex.exp ((hexPhase_sideTilt headTm : ℝ) * Complex.I) * ((hexBdryCt * taum : ℝ) : ℂ)
  

  phaseU : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 4),
        D.obs (D.mid e.vtx e.edge))
      = 2 * Complex.exp ((hexPhase_sideTilt headU : ℝ) * Complex.I) * ((ups : ℝ) : ℂ)

end StatMech.Universality
