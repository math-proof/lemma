/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Mathlib.Topology.Constructions
import Mathlib.Topology.UnitInterval
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section6
open Finset BigOperators


namespace AlgebraicTopologyI

/-- The continuous `i`-th face inclusion `Δⁿ ↪ Δⁿ⁺¹` that sends the barycentric
coordinates `t` to the tuple with `0` inserted in position `i`. -/
noncomputable def faceInclusion (n : ℕ) (i : Fin (n + 2)) :
    C(↥(stdSimplex ℝ (Fin (n + 1))), ↥(stdSimplex ℝ (Fin (n + 2)))) where
  toFun t := ⟨Fin.insertNth i 0 t.1, faceMap_mem_stdSimplex n i t.1 t.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Continuous.finInsertNth i continuous_const continuous_subtype_val

/-- The `i`-th face of a singular `(n+1)`-simplex `σ`, obtained by precomposing with the
`i`-th face inclusion of the standard simplex. -/
noncomputable def SingularSimplex.face {n : ℕ} {X : Type*} [TopologicalSpace X]
    (i : Fin (n + 2)) (σ : SingularSimplex (n + 1) X) : SingularSimplex n X :=
  σ.comp (faceInclusion n i)

/-- The singular boundary map `d : S_{n+1}(X) → S_n(X)` defined on generators by the
alternating sum `∑_i (-1)^i σ ∘ d^i` of face restrictions. -/
noncomputable def boundaryMap (n : ℕ) (X : Type*) [TopologicalSpace X] :
    SingularChains (n + 1) X →+ SingularChains n X :=
  FreeAbelianGroup.lift (fun σ =>
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • FreeAbelianGroup.of (SingularSimplex.face i σ))

/-- Pushforward of a singular `n`-simplex along a continuous map `f : X → Y`, namely
`f ∘ σ`. -/
noncomputable def SingularSimplex.map {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (σ : SingularSimplex n X) : SingularSimplex n Y :=
  f.comp σ

/-- The induced map on singular chains `f_* : S_n(X) → S_n(Y)`, extending the
pushforward of simplices linearly. -/
noncomputable def SingularChains.map {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : SingularChains n X →+ SingularChains n Y :=
  FreeAbelianGroup.map (SingularSimplex.map f)

/-- The slice inclusion `j_x : Y → X × Y`, `y ↦ (x, y)`. -/
noncomputable def inclusionRight {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) : C(Y, X × Y) :=
  ContinuousMap.prodMk (ContinuousMap.const Y x) (ContinuousMap.id Y)

/-- The slice inclusion `i_y : X → X × Y`, `x ↦ (x, y)`. -/
noncomputable def inclusionLeft {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (y : Y) : C(X, X × Y) :=
  ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X y)

/-- The constant `0`-simplex `c_x^0 : Δ^0 → X` at the point `x`. -/
noncomputable def constSimplex {X : Type*} [TopologicalSpace X] (x : X) :
    SingularSimplex 0 X :=
  ContinuousMap.const _ x

/-- The constant `0`-chain at `x`, namely the generator of `S_0(X)` corresponding to the
constant simplex `c_x^0`. -/
noncomputable def constChain {X : Type*} [TopologicalSpace X] (x : X) :
    SingularChains 0 X :=
  FreeAbelianGroup.of (constSimplex x)

/-- Trivial reindexing isomorphism `S_n(X) → S_m(X)` along an equality `n = m`. Used to
identify chains living in defeq-but-not-syntactically-equal degrees. -/
noncomputable def SingularChains.castIdx {n m : ℕ} (h : n = m) {X : Type*}
    [TopologicalSpace X] : SingularChains n X →+ SingularChains m X :=
  h ▸ AddMonoidHom.id _

end AlgebraicTopologyI
