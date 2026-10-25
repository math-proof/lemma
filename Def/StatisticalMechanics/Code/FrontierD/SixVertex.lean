/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Hom.PowersetCard
import Structure.StatisticalMechanics.Code.FrontierD.SixVertex.Part2
open Finset Matrix


namespace StatMech.FrontierD

namespace SixVertexArrows

variable {T : EvenTorus}


def cyclicPred {N : ℕ} (hN : 0 < N) (i : Fin N) : Fin N :=
  ⟨(i.val + N - 1) % N, Nat.mod_lt _ hN⟩


def incomingCount (ω : SixVertexArrows T) (v : T.Vertex) : ℕ :=
  (ω.horizontal (cyclicPred T.width_pos v.1, v.2)).toNat + (!ω.horizontal v).toNat +
    (ω.vertical (v.1, cyclicPred T.height_pos v.2)).toNat + (!ω.vertical v).toNat


def IceRule (ω : SixVertexArrows T) : Prop :=
  ∀ v, ω.incomingCount v = 2


def IsCType (ω : SixVertexArrows T) (v : T.Vertex) : Prop :=
  ((ω.horizontal (cyclicPred T.width_pos v.1, v.2)).toNat +
      (!ω.horizontal v).toNat = 0) ∨
    ((ω.horizontal (cyclicPred T.width_pos v.1, v.2)).toNat +
      (!ω.horizontal v).toNat = 2)


noncomputable def localWeight (c : ℝ) (ω : SixVertexArrows T) (v : T.Vertex) : ℝ := by
  classical
  exact if ω.incomingCount v = 2 then if ω.IsCType v then c else 1 else 0


noncomputable def weight (c : ℝ) (ω : SixVertexArrows T) : ℝ :=
  ∏ v, ω.localWeight c v

end SixVertexArrows
end StatMech.FrontierD
