/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusCrossingEvents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem FKRectConnectedWithin.mono_configuration
    (R : FKRectTorus) {omega tau : R.Configuration}
    (hopen : omega ≤ tau) (S : Set R.Vertex) {x y : S}
    (hxy : FKRectConnectedWithin R omega S x y) :
    FKRectConnectedWithin R tau S x y := by
  apply hxy.mono
  intro u v huv
  exact fkRectOpenGraph_mono R (omega := omega) (tau := tau) (by
    intro e he
    cases het : tau e
    · have hle := hopen e
      rw [he, het] at hle
      exact ((by decide : ¬ (true ≤ false)) hle).elim
    · rfl) huv


theorem fkRectConnectedWithin_isIncreasing
    (R : FKRectTorus) (S : Set R.Vertex) (x y : S) :
    IsIncreasing
      {omega : R.Configuration | FKRectConnectedWithin R omega S x y} := by
  intro omega tau hopen hxy
  exact hxy.mono_configuration R hopen S


theorem FKRectConnectedWithin.mono_set
    (R : FKRectTorus) (omega : R.Configuration)
    {S T : Set R.Vertex} (hST : S ⊆ T) {x y : S}
    (hxy : FKRectConnectedWithin R omega S x y) :
    FKRectConnectedWithin R omega T
      ⟨x, hST x.2⟩ ⟨y, hST y.2⟩ := by
  exact hxy.map
    ((fkRectOpenGraph R omega).induceHomOfLE hST).toHom


theorem FKRectConnectedWithin.trans_union
    (R : FKRectTorus) (omega : R.Configuration)
    {S T : Set R.Vertex} {x y z : R.Vertex}
    (hx : x ∈ S) (hyS : y ∈ S) (hyT : y ∈ T) (hz : z ∈ T)
    (hxy : FKRectConnectedWithin R omega S ⟨x, hx⟩ ⟨y, hyS⟩)
    (hyz : FKRectConnectedWithin R omega T ⟨y, hyT⟩ ⟨z, hz⟩) :
    FKRectConnectedWithin R omega (S ∪ T)
      ⟨x, Or.inl hx⟩ ⟨z, Or.inr hz⟩ := by
  have hxy' := hxy.mono_set R omega
    (T := S ∪ T) (fun _ h => Or.inl h)
  have hyz' := hyz.mono_set R omega
    (T := S ∪ T) (fun _ h => Or.inr h)
  exact hxy'.trans hyz'


end
end StatMech.FrontierD
