/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardMetricClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardAtlas
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardMetricClosure.Part3
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u

variable {E D Q : Type*} [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]


namespace MetricCriticalIsoradialClosedFlatSurfaceEmbedding

variable {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {DualVertex Qprimal Qdual : Type u}
  [Fintype DualVertex] [DecidableEq DualVertex]
  [Fintype Qprimal] [DecidableEq Qprimal]
  [Fintype Qdual] [DecidableEq Qdual]


@[simp] theorem primalExceptional_iff
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual) (vertex : V) :
    embedding.primalExceptional vertex = true ↔
      embedding.primalConeIndex vertex % 2 = 1 := by
  simp [primalExceptional]

@[simp] theorem dualExceptional_iff
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual) (vertex : DualVertex) :
    embedding.dualExceptional vertex = true ↔
      embedding.dualConeIndex vertex % 2 = 1 := by
  simp [dualExceptional]


theorem coneIndexGaussBonnet
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual) :
    (∑ vertex : V, embedding.primalConeIndex vertex) +
      (∑ vertex : DualVertex, embedding.dualConeIndex vertex) + 1 = g := by
  have hprimal :
      (∑ vertex : V, ∑ edge : finiteGraphEdge G,
        (embedding.primalRhombusIncidence vertex edge : Real) *
          embedding.theta edge) =
      ∑ vertex : V,
        Real.pi *
          (2 * (embedding.primalConeIndex vertex : Real) + 1) := by
    apply Finset.sum_congr rfl
    intro vertex _
    exact embedding.primalConeAngle vertex
  have hdual :
      (∑ vertex : DualVertex, ∑ edge : finiteGraphEdge G,
        (embedding.dualRhombusIncidence vertex edge : Real) *
          (Real.pi / 2 - embedding.theta edge)) =
      ∑ vertex : DualVertex,
        Real.pi *
          (2 * (embedding.dualConeIndex vertex : Real) + 1) := by
    apply Finset.sum_congr rfl
    intro vertex _
    exact embedding.dualConeAngle vertex
  have hprimalTotal :
      (∑ vertex : V, ∑ edge : finiteGraphEdge G,
        (embedding.primalRhombusIncidence vertex edge : Real) *
          embedding.theta edge) =
      2 * ∑ edge : finiteGraphEdge G, embedding.theta edge := by
    rw [Finset.sum_comm]
    calc
      (∑ edge : finiteGraphEdge G, ∑ vertex : V,
          (embedding.primalRhombusIncidence vertex edge : Real) *
            embedding.theta edge) =
          ∑ edge : finiteGraphEdge G,
            ((∑ vertex : V,
              embedding.primalRhombusIncidence vertex edge : Nat) : Real) *
              embedding.theta edge := by
        apply Finset.sum_congr rfl
        intro edge _
        push_cast
        rw [Finset.sum_mul]
      _ = ∑ edge : finiteGraphEdge G, 2 * embedding.theta edge := by
        apply Finset.sum_congr rfl
        intro edge _
        rw [embedding.primalRhombusIncidence_total edge]
        norm_num
      _ = _ := by rw [Finset.mul_sum]
  have hdualTotal :
      (∑ vertex : DualVertex, ∑ edge : finiteGraphEdge G,
        (embedding.dualRhombusIncidence vertex edge : Real) *
          (Real.pi / 2 - embedding.theta edge)) =
      2 * ∑ edge : finiteGraphEdge G,
        (Real.pi / 2 - embedding.theta edge) := by
    rw [Finset.sum_comm]
    calc
      (∑ edge : finiteGraphEdge G, ∑ vertex : DualVertex,
          (embedding.dualRhombusIncidence vertex edge : Real) *
            (Real.pi / 2 - embedding.theta edge)) =
          ∑ edge : finiteGraphEdge G,
            ((∑ vertex : DualVertex,
              embedding.dualRhombusIncidence vertex edge : Nat) : Real) *
              (Real.pi / 2 - embedding.theta edge) := by
        apply Finset.sum_congr rfl
        intro edge _
        push_cast
        rw [Finset.sum_mul]
      _ = ∑ edge : finiteGraphEdge G,
          2 * (Real.pi / 2 - embedding.theta edge) := by
        apply Finset.sum_congr rfl
        intro edge _
        rw [embedding.dualRhombusIncidence_total edge]
        norm_num
      _ = _ := by rw [Finset.mul_sum]
  have hedgeAngles :
      (2 * ∑ edge : finiteGraphEdge G, embedding.theta edge) +
        (2 * ∑ edge : finiteGraphEdge G,
          (Real.pi / 2 - embedding.theta edge)) =
        (Fintype.card (finiteGraphEdge G) : Real) * Real.pi := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hconeAngles :
      (∑ vertex : V,
          Real.pi *
            (2 * (embedding.primalConeIndex vertex : Real) + 1)) +
        (∑ vertex : DualVertex,
          Real.pi *
            (2 * (embedding.dualConeIndex vertex : Real) + 1)) =
        (Fintype.card (finiteGraphEdge G) : Real) * Real.pi := by
    rw [← hprimal, ← hdual, hprimalTotal, hdualTotal]
    exact hedgeAngles
  have heuler := embedding.polygonalAtlas.cellular.cellularEuler
  rw [embedding.dualVertexCount_eq,
    embedding.polygonalAtlas.genus_eq] at heuler
  have hedgeCard :
      Fintype.card (finiteGraphEdge G) = G.edgeFinset.card := by
    exact Fintype.card_coe G.edgeFinset
  rw [hedgeCard] at hconeAngles
  simp only [mul_add, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hconeAngles
  have hfactor (x : Real) : Real.pi * (2 * x) =
      (2 * Real.pi) * x := by ring
  simp_rw [hfactor] at hconeAngles
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hconeAngles
  have heulerReal :
      (Fintype.card V : Real) + (Fintype.card DualVertex : Real) +
          2 * (g : Real) =
        (G.edgeFinset.card : Real) + 2 := by
    exact_mod_cast heuler
  have hreal :
      ((∑ vertex : V, embedding.primalConeIndex vertex) : Real) +
        ((∑ vertex : DualVertex,
          embedding.dualConeIndex vertex) : Real) + 1 = (g : Real) := by
    nlinarith [Real.pi_pos, heulerReal]
  exact_mod_cast hreal


end MetricCriticalIsoradialClosedFlatSurfaceEmbedding
end StatMech.FrontierA
