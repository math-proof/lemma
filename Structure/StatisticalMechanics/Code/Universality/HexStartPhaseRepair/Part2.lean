/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part2


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


structure HexFiniteStripFourPhaseData
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing} (C : HexFiniteStripBoundaryCore R h0 D P)
    (G : HexRegion) where
  
  start_eq : G.start = R.start
  
  heading : V → Fin 3 → ℤ
  
  hgeom : ∀ v j,
    D.mid v j - D.pos v = (1 / 2 : ℂ) * hexUnit (heading v j)
  
  startIncidence : HexIncidence V
  
  startFiber_singleton :
    (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 0) = {startIncidence}
  
  start_mid : D.mid startIncidence.vtx startIncidence.edge = G.start
  
  start_heading : heading startIncidence.vtx startIncidence.edge = 4
  
  headL : ℤ
  headTp : ℤ
  headTm : ℤ
  headU : ℤ
  hHeadL : ∀ e ∈ (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 1),
    heading e.vtx e.edge = headL
  hHeadTp : ∀ e ∈ (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 2),
    heading e.vtx e.edge = headTp
  hHeadTm : ∀ e ∈ (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 3),
    heading e.vtx e.edge = headTm
  hHeadU : ∀ e ∈ (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 4),
    heading e.vtx e.edge = headU
  
  taup : ℝ
  taum : ℝ
  tau_eq : taup + taum = C.tau
  
  phaseL : (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 1),
      D.obs (D.mid e.vtx e.edge)) =
    Complex.exp ((hexPhase_sideTilt headL : ℝ) * Complex.I)
      * ((hexBdryCl * C.lam : ℝ) : ℂ)
  
  phaseTp : (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 2),
      D.obs (D.mid e.vtx e.edge)) =
    Complex.exp ((hexPhase_sideTilt headTp : ℝ) * Complex.I)
      * ((hexBdryCt * taup : ℝ) : ℂ)
  
  phaseTm : (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 3),
      D.obs (D.mid e.vtx e.edge)) =
    Complex.exp ((hexPhase_sideTilt headTm : ℝ) * Complex.I)
      * ((hexBdryCt * taum : ℝ) : ℂ)
  
  phaseU : (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 4),
      D.obs (D.mid e.vtx e.edge)) =
    Complex.exp ((hexPhase_sideTilt headU : ℝ) * Complex.I)
      * ((C.ups : ℝ) : ℂ)

end StatMech.Universality
