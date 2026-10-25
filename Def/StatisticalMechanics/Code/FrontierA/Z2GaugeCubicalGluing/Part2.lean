/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSubsystem.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeRectangularThermodynamic
import Theorem.StatisticalMechanics.Code.FrontierA.RectangularBlockTiling
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part2
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.flexible false


namespace StatMech.FrontierA

noncomputable section

variable {E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

variable {Esmall Ebig Psmall Pbig : Type*}
  [Fintype Esmall] [DecidableEq Esmall] [Fintype Ebig] [DecidableEq Ebig]
  [Fintype Psmall] [DecidableEq Psmall] [Fintype Pbig] [DecidableEq Pbig]

def cubicalEdgeChart {a b c A B C : Nat} (ox oy oz : Nat)
    (hx : ox + a ≤ A) (hy : oy + b ≤ B) (hz : oz + c ≤ C) :
    CubicalEdge a b c ↪ CubicalEdge A B C where
  toFun
    | .x i j k => .x (finOffsetEmbedding ox hx i)
        (finOffsetEmbedding oy (by omega) j)
        (finOffsetEmbedding oz (by omega) k)
    | .y i j k => .y (finOffsetEmbedding ox (by omega) i)
        (finOffsetEmbedding oy hy j)
        (finOffsetEmbedding oz (by omega) k)
    | .z i j k => .z (finOffsetEmbedding ox (by omega) i)
        (finOffsetEmbedding oy (by omega) j)
        (finOffsetEmbedding oz hz k)
  inj' := by
    intro e f hef
    cases e <;> cases f <;>
      simp only [CubicalEdge.x.injEq, CubicalEdge.y.injEq,
        CubicalEdge.z.injEq, reduceCtorEq] at hef ⊢ <;>
      simp_all [finOffsetEmbedding]

def cubicalPlaquetteChart {a b c A B C : Nat} (ox oy oz : Nat)
    (hx : ox + a ≤ A) (hy : oy + b ≤ B) (hz : oz + c ≤ C) :
    CubicalPlaquette a b c ↪ CubicalPlaquette A B C where
  toFun
    | .xy i j k => .xy (finOffsetEmbedding ox hx i)
        (finOffsetEmbedding oy hy j)
        (finOffsetEmbedding oz (by omega) k)
    | .xz i j k => .xz (finOffsetEmbedding ox hx i)
        (finOffsetEmbedding oy (by omega) j)
        (finOffsetEmbedding oz hz k)
    | .yz i j k => .yz (finOffsetEmbedding ox (by omega) i)
        (finOffsetEmbedding oy hy j)
        (finOffsetEmbedding oz hz k)
  inj' := by
    intro p q hpq
    cases p <;> cases q <;>
      simp only [CubicalPlaquette.xy.injEq, CubicalPlaquette.xz.injEq,
        CubicalPlaquette.yz.injEq, reduceCtorEq] at hpq ⊢ <;>
      simp_all [finOffsetEmbedding]

end
end StatMech.FrontierA
