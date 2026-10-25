/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.FK.TwoPointInfinite.Part5
import Theorem.StatisticalMechanics.Code.FK.BoxTailLimit
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.FreeWiredAgreeClose.Part3
import Theorem.StatisticalMechanics.Code.Ising.TransitionFK
open Filter
open MeasureTheory


namespace StatMech

namespace Exact3D

open FK


def ising3DOriginBoxVertex (n : ℕ) : boxVerts 3 n :=
  ⟨ising3DOrigin, ising3DOrigin_mem_box n⟩


def ising3DXAxisBoxVertex (n : ℕ) : boxVerts 3 n :=
  ⟨ising3DXAxisRay n, ising3DXAxisRay_mem_box_self n⟩


def ising3DXAxisBoxVertexInBox (N n : ℕ) (h : n ≤ N) : boxVerts 3 N :=
  ⟨ising3DXAxisRay n, ising3DXAxisRay_mem_box_le h⟩


noncomputable def freeFiniteVolumeXAxisConnectionQ2
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (n : ℕ) : ℝ :=
  ((freeFiniteMeasure 3 n hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
    (boxConnEvent 3 n (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n)))


noncomputable def wiredFiniteVolumeXAxisConnectionQ2
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (n : ℕ) : ℝ :=
  ((wiredFiniteMeasure 3 n hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
    (boxConnEvent 3 n (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n)))


noncomputable def freeInfiniteVolumeXAxisConnectionQ2
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (n : ℕ) : ℝ :=
  ((freeInfiniteVolume 3 hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
    (boxConnEvent 3 n (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n)))


noncomputable def wiredInfiniteVolumeXAxisConnectionQ2
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (n : ℕ) : ℝ :=
  ((wiredInfiniteVolume 3 hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
    (boxConnEvent 3 n (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n)))


noncomputable def freeInfiniteVolumeXAxisConnectionOfBetaQ2
    (β : ℝ) (hβ : 0 < β) (n : ℕ) : ℝ :=
  freeInfiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
    (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) n


noncomputable def freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume
    (β : ℝ) (hβ : 0 < β) (N n : ℕ) : ℝ :=
  ((freeFiniteMeasure 3 N (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
      (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
    (boxConnEvent 3 n (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n)))


noncomputable def freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume
    (β : ℝ) (hβ : 0 < β) (N n : ℕ) : ℝ :=
  if hn : n ≤ N then
    ((freeFiniteMeasure 3 N (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
        (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
      (boxConnEvent 3 N (ising3DOriginBoxVertex N)
        (ising3DXAxisBoxVertexInBox N n hn)))
  else
    0


noncomputable def wiredInfiniteVolumeXAxisConnectionOfBetaQ2
    (β : ℝ) (hβ : 0 < β) (n : ℕ) : ℝ :=
  wiredInfiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
    (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) n


def FreeXAxisQ2ConnectionAgrees (β : ℝ) (hβ : 0 < β) : Prop :=
  FreeXAxisFKConnectionAgrees β
    (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ)


def FreeXAxisWiredQ2ConnectionAgrees (β : ℝ) (hβ : 0 < β) : Prop :=
  FreeXAxisFKConnectionAgrees β
    (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ)


def PlusXAxisWiredQ2ConnectionAgrees (β : ℝ) (hβ : 0 < β) : Prop :=
  PlusXAxisFKConnectionAgrees β
    (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ)


end Exact3D
end StatMech
