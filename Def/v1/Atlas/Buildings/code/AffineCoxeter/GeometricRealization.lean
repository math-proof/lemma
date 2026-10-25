/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/GeometricRealization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex.Part2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Structure.v1.Atlas.Buildings.code.AffineCoxeter.GeometricRealization
set_option linter.unusedSectionVars false


noncomputable section

open Finset BigOperators

namespace GeometricRealization

variable {V : Type*} [DecidableEq V] [Fintype V] [Nonempty V]

/-- $\ell^\infty$ distance between two points in $|\Delta|$: the supremum of $|p_v - q_v|$ over $v$. -/
noncomputable def dist {Δ : SimplicialComplex V} (p q : Point Δ) : ℝ :=
  Finset.univ.sup' ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    (fun v => |p.wt v - q.wt v|)

/-- The canonical embedding of a vertex $v$ as the corresponding $\delta_v$-point of $|\Delta|$. -/
noncomputable def vertexEmbedding (Δ : SimplicialComplex V) (v : V)
    (hv : {v} ∈ Δ.faces) : Point Δ where
  wt := fun w => if w = v then 1 else 0
  wt_nonneg := by intro w; split_ifs <;> norm_num
  wt_sum := by simp [Finset.sum_ite_eq']
  support_in_face := by
    refine ⟨{v}, hv, fun w hw => ?_⟩
    simp only [Finset.mem_singleton]
    by_contra h
    apply hw
    simp only [ite_eq_right_iff]
    intro heq
    exact absurd heq h

/-- The support of a point $p \in |\Delta|$: the (necessarily finite) set $\{v : p_v \ne 0\}$. -/
def support {Δ : SimplicialComplex V} (p : Point Δ) : Finset V :=
  Finset.univ.filter (fun v => p.wt v ≠ 0)

/-- Vertex-realization: given a vertex map $i : V \to Z$ into an $\mathbb R$-module, extend to the
geometric realization $|\Delta| \to Z$ by barycentric combinations $p \mapsto \sum_v p_v \cdot i(v)$. -/
noncomputable def vertexRealizationMap {Δ : SimplicialComplex V}
    {Z : Type*} [AddCommMonoid Z] [Module ℝ Z]
    (i : V → Z) (p : Point Δ) : Z :=
  ∑ v : V, p.wt v • i v

end GeometricRealization
end
