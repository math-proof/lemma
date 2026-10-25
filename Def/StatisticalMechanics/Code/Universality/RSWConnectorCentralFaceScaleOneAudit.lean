/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceScaleOneAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFiniteGraph.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def axisReturn_v0 : rect (-2) 0 (-1) 1 :=
  ⟨![-2, 0], by simp [mem_rect]⟩

def axisReturn_v1 : rect (-2) 0 (-1) 1 :=
  ⟨![-2, 1], by simp [mem_rect]⟩

def axisReturn_v2 : rect (-2) 0 (-1) 1 :=
  ⟨![-1, 1], by simp [mem_rect]⟩

def axisReturn_v3 : rect (-2) 0 (-1) 1 :=
  ⟨![-1, 0], by simp [mem_rect]⟩

def axisReturn_v4 : rect (-2) 0 (-1) 1 :=
  ⟨![0, 0], by simp [mem_rect]⟩

def axisReturn_v5 : rect (-2) 0 (-1) 1 :=
  ⟨![0, 1], by simp [mem_rect]⟩

end
end StatMech.Universality
