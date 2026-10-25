/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalWitnessStep.Part2
import Theorem.StatisticalMechanics.Code.Probability.AdaptiveFibreStep
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part4
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


theorem fkRectPrimalAdaptiveProjection_le
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) :
    fkRectPrimalAdaptiveProjection R S rho ≤ rho := by
  intro e
  unfold fkRectPrimalAdaptiveProjection FK.projOff
  by_cases he : e ∈ fkRectPrimalAdaptiveInsideEdges R S rho
  · simp [he]
  · simp [he]

theorem fkRectPrimalAdaptiveProjection_eq_of_not_mem
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) {e : Sym2 R.Vertex}
    (he : e ∉ fkRectPrimalAdaptiveInsideEdges R S rho) :
    fkRectPrimalAdaptiveProjection R S rho e = rho e := by
  unfold fkRectPrimalAdaptiveProjection FK.projOff
  simp [he]


theorem not_mem_fkRectPrimalFullUnexploredPairEdges_of_explored_left
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) {x y : R.Vertex}
    (hx : FKRectPrimalFullExploredVertex R S rho x) :
    s(x, y) ∉ fkRectPrimalFullUnexploredPairEdges R S rho := by
  intro hmem
  rcases (mem_fkRectPrimalFullUnexploredPairEdges_iff R S rho _).1 hmem with
    ⟨u, v, huv, hu, hv⟩
  rcases Sym2.eq_iff.mp huv with ⟨hxu, _⟩ | ⟨hxv, _⟩
  · exact hu (hxu ▸ hx)
  · exact hv (hxv ▸ hx)


theorem fkRectPrimalAdaptiveProjection_openAdj_of_explored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) {x y : R.Vertex}
    (hx : FKRectPrimalFullExploredVertex R S rho x)
    (hxy : (FK.openSub (fkRectCutGraph R) rho).Adj x y) :
    (FK.openSub (fkRectCutGraph R)
      (fkRectPrimalAdaptiveProjection R S rho)).Adj x y := by
  refine ⟨hxy.1, ?_⟩
  have hpair : s(x, y) ∉ fkRectPrimalFullUnexploredPairEdges R S rho :=
    not_mem_fkRectPrimalFullUnexploredPairEdges_of_explored_left
      R S rho hx
  have hinside : s(x, y) ∉ fkRectPrimalAdaptiveInsideEdges R S rho := by
    exact hpair
  rw [fkRectPrimalAdaptiveProjection_eq_of_not_mem R S rho hinside]
  exact hxy.2


theorem fkRectPrimalFullExploredVertex_projection_of_explored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) {v : R.Vertex}
    (hv : FKRectPrimalFullExploredVertex R S rho v) :
    FKRectPrimalFullExploredVertex R S
      (fkRectPrimalAdaptiveProjection R S rho) v := by
  rcases hv with ⟨i, hi, hreach⟩
  refine ⟨i, hi, ?_⟩
  let source : R.Vertex := (fkRectLeftColumn R, i)
  let G := FK.openSub (fkRectCutGraph R) rho
  let H := FK.openSub (fkRectCutGraph R)
    (fkRectPrimalAdaptiveProjection R S rho)
  let liftWalk : ∀ {x y : R.Vertex}, G.Walk x y →
      G.Reachable source x → H.Walk x y := by
    intro x y path
    induction path with
    | nil => intro _; exact SimpleGraph.Walk.nil
    | @cons x y z hxy path ih =>
        intro hsx
        exact SimpleGraph.Walk.cons
          (fkRectPrimalAdaptiveProjection_openAdj_of_explored R S rho
            ⟨i, hi, hsx⟩ hxy)
          (ih (hsx.trans hxy.reachable))
  exact hreach.elim fun path =>
    ⟨liftWalk path (SimpleGraph.Reachable.refl source)⟩


theorem fkRectPrimalFullExploredVertex_of_projection
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) {v : R.Vertex}
    (hv : FKRectPrimalFullExploredVertex R S
      (fkRectPrimalAdaptiveProjection R S rho) v) :
    FKRectPrimalFullExploredVertex R S rho v := by
  rcases hv with ⟨i, hi, hreach⟩
  exact ⟨i, hi, hreach.mono (FK.openSub_mono _
    (fkRectPrimalAdaptiveProjection_le R S rho))⟩


theorem fkRectPrimalFullExploredVertex_projection_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) (v : R.Vertex) :
    FKRectPrimalFullExploredVertex R S
        (fkRectPrimalAdaptiveProjection R S rho) v ↔
      FKRectPrimalFullExploredVertex R S rho v :=
  ⟨fkRectPrimalFullExploredVertex_of_projection R S rho,
    fkRectPrimalFullExploredVertex_projection_of_explored R S rho⟩

theorem fkRectPrimalAdaptiveInsideEdges_projection
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) :
    fkRectPrimalAdaptiveInsideEdges R S
        (fkRectPrimalAdaptiveProjection R S rho) =
      fkRectPrimalAdaptiveInsideEdges R S rho := by
  unfold fkRectPrimalAdaptiveInsideEdges
  ext e
  rw [mem_fkRectPrimalFullUnexploredPairEdges_iff,
    mem_fkRectPrimalFullUnexploredPairEdges_iff]
  constructor
  · rintro ⟨x, y, he, hx, hy⟩
    exact ⟨x, y, he,
      fun h => hx ((fkRectPrimalFullExploredVertex_projection_iff R S rho x).2 h),
      fun h => hy ((fkRectPrimalFullExploredVertex_projection_iff R S rho y).2 h)⟩
  · rintro ⟨x, y, he, hx, hy⟩
    exact ⟨x, y, he,
      fun h => hx ((fkRectPrimalFullExploredVertex_projection_iff R S rho x).1 h),
      fun h => hy ((fkRectPrimalFullExploredVertex_projection_iff R S rho y).1 h)⟩


theorem fkRectPrimalAdaptiveProjection_idem
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) :
    fkRectPrimalAdaptiveProjection R S
        (fkRectPrimalAdaptiveProjection R S rho) =
      fkRectPrimalAdaptiveProjection R S rho := by
  change FK.projOff
      (fkRectPrimalAdaptiveInsideEdges R S
        (fkRectPrimalAdaptiveProjection R S rho))
      (fkRectPrimalAdaptiveProjection R S rho) =
    fkRectPrimalAdaptiveProjection R S rho
  rw [fkRectPrimalAdaptiveInsideEdges_projection]
  unfold fkRectPrimalAdaptiveProjection
  exact FK.projOff_idem _ _


end
end StatMech.FrontierD
