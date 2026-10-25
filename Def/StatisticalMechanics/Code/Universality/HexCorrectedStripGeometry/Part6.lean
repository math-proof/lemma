/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Instance.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part2


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexCSIncidences (T L : ℕ) : Finset (HexCSIncidence T L) :=
  ((Finset.univ : Finset (HexCSVertex T L)) ×ˢ
      (Finset.univ : Finset (Fin 3))).image
    (fun p => ⟨p.1, p.2⟩)

def hexCSInteriorIncidences (T L : ℕ) : Finset (HexCSIncidence T L) :=
  (hexCSIncidences T L).filter hexCSIsInterior

def hexCSBoundaryIncidences (T L : ℕ) : Finset (HexCSIncidence T L) :=
  hexCSIncidences T L \ hexCSInteriorIncidences T L

end
end StatMech.Universality
