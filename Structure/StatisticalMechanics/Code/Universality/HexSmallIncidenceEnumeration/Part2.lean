/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexSmallIncidenceEnumeration.Part3


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


structure HexFiniteStripCoreOrientation
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (C : HexFiniteStripBoundaryCore R h0 D P) where
  heading : V → Fin 3 → ℤ
  hgeom : ∀ v j,
    D.mid v j - D.pos v = (1 / 2 : ℂ) * hexUnit (heading v j)
  startIncidence : HexIncidence V
  startFiber_singleton :
    hexFiniteStripPhysicalStartFiber (R := R) P = {startIncidence}
  start_mid : D.mid startIncidence.vtx startIncidence.edge = R.start
  start_heading : heading startIncidence.vtx startIncidence.edge = 4
  headL : ℤ
  headTp : ℤ
  headTm : ℤ
  headU : ℤ
  hHeadL : ∀ e ∈ D.incidences \ P.interior,
    D.mid e.vtx e.edge ∈ C.sides.bottom →
      heading e.vtx e.edge = headL
  hHeadTp : ∀ e ∈ D.incidences \ P.interior,
    D.mid e.vtx e.edge ∈ C.sides.slantPlus →
      heading e.vtx e.edge = headTp
  hHeadTm : ∀ e ∈ D.incidences \ P.interior,
    D.mid e.vtx e.edge ∈ C.sides.slantMinus →
      heading e.vtx e.edge = headTm
  hHeadU : ∀ e ∈ D.incidences \ P.interior,
    D.mid e.vtx e.edge ∈ C.sides.top →
      heading e.vtx e.edge = headU


structure HexFiniteStripFourPhaseLiftData
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    {C : HexFiniteStripBoundaryCore R h0 D P}
    (O : HexFiniteStripCoreOrientation C) (G : HexRegion) where
  start_eq : G.start = R.start
  class_eq : ∀ e ∈ D.incidences \ P.interior, ∀ k : Fin 5,
    hexRegionClsInc G D e = k ↔
      hexFiniteStripCoreContourPart C k (D.mid e.vtx e.edge)
  taup : ℝ
  taum : ℝ
  tau_eq : taup + taum = C.tau
  phaseL : (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 1),
      D.obs (D.mid e.vtx e.edge)) =
    Complex.exp ((hexPhase_sideTilt O.headL : ℝ) * Complex.I)
      * ((hexBdryCl * C.lam : ℝ) : ℂ)
  phaseTp : (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 2),
      D.obs (D.mid e.vtx e.edge)) =
    Complex.exp ((hexPhase_sideTilt O.headTp : ℝ) * Complex.I)
      * ((hexBdryCt * taup : ℝ) : ℂ)
  phaseTm : (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 3),
      D.obs (D.mid e.vtx e.edge)) =
    Complex.exp ((hexPhase_sideTilt O.headTm : ℝ) * Complex.I)
      * ((hexBdryCt * taum : ℝ) : ℂ)
  phaseU : (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 4),
      D.obs (D.mid e.vtx e.edge)) =
    Complex.exp ((hexPhase_sideTilt O.headU : ℝ) * Complex.I)
      * ((C.ups : ℝ) : ℂ)

end StatMech.Universality
