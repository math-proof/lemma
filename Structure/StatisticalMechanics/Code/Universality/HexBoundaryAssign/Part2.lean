/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFamilyAssign.Part3
import Def.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part2


namespace StatMech.Universality

open Complex

open scoped BigOperators


variable {V : Type*} [DecidableEq V]


structure HexRegionAssign (D : HexDomain V) (P : D.InteriorPairing) (R : HexRegion) where
  
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
  
  projA : ((1 / 2 : ℂ) * hexUnit headA) *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 0),
        D.obs (D.mid e.vtx e.edge))
      = Complex.I * (((-1 : ℝ) * Fa : ℝ) : ℂ)
  
  projL : ((1 / 2 : ℂ) * hexUnit headL) *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 1),
        D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((hexBdryCl * lam : ℝ) : ℂ)
  
  projTp : ((1 / 2 : ℂ) * hexUnit headTp) *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 2),
        D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((hexBdryCt * taup : ℝ) : ℂ)
  
  projTm : ((1 / 2 : ℂ) * hexUnit headTm) *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 3),
        D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((hexBdryCt * taum : ℝ) : ℂ)
  
  projU : ((1 / 2 : ℂ) * hexUnit headU) *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 4),
        D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((ups : ℝ) : ℂ)

end StatMech.Universality
