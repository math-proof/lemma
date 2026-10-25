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
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part5
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


theorem fkRectPrimalSourceReachable_projection_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex))
    {i : Fin R.height} (hi : i ∈ S) (v : R.Vertex) :
    (FK.openSub (fkRectCutGraph R)
        (fkRectPrimalAdaptiveProjection R S rho)).Reachable
        (fkRectLeftColumn R, i) v ↔
      (FK.openSub (fkRectCutGraph R) rho).Reachable
        (fkRectLeftColumn R, i) v := by
  constructor
  · intro hreach
    exact hreach.mono (FK.openSub_mono _
      (fkRectPrimalAdaptiveProjection_le R S rho))
  · intro hreach
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


theorem fkRectPrimalFullDistinctCrossingWitness_projection_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) :
    FKRectPrimalFullDistinctCrossingWitness R S
        (fkRectPrimalAdaptiveProjection R S rho) ↔
      FKRectPrimalFullDistinctCrossingWitness R S rho := by
  constructor
  · rintro ⟨hcross, hdistinct⟩
    constructor
    · intro i hi
      rcases hcross i hi with ⟨z, hiz⟩
      exact ⟨z,
        (fkRectPrimalSourceReachable_projection_iff R S rho hi _).1 hiz⟩
    · intro i hi j hj hij hreach
      apply hdistinct i hi j hj hij
      exact (fkRectPrimalSourceReachable_projection_iff R S rho hi _).2 hreach
  · rintro ⟨hcross, hdistinct⟩
    constructor
    · intro i hi
      rcases hcross i hi with ⟨z, hiz⟩
      exact ⟨z,
        (fkRectPrimalSourceReachable_projection_iff R S rho hi _).2 hiz⟩
    · intro i hi j hj hij hreach
      apply hdistinct i hi j hj hij
      exact (fkRectPrimalSourceReachable_projection_iff R S rho hi _).1 hreach


theorem fkRectPrimalFullDistinctCrossingWitness_fibre_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    {rho sigma : ConfigSpace (Sym2 R.Vertex)}
    (hproj : fkRectPrimalAdaptiveProjection R S rho =
      fkRectPrimalAdaptiveProjection R S sigma) :
    FKRectPrimalFullDistinctCrossingWitness R S rho ↔
      FKRectPrimalFullDistinctCrossingWitness R S sigma := by
  rw [← fkRectPrimalFullDistinctCrossingWitness_projection_iff R S rho,
    ← fkRectPrimalFullDistinctCrossingWitness_projection_iff R S sigma,
    hproj]


theorem fkRectPrimalSourceReachable_agreesOff_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (psi rho : ConfigSpace (Sym2 R.Vertex))
    (hagree : FK.AgreesOff
      (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho)
    {i : Fin R.height} (hi : i ∈ S) (v : R.Vertex) :
    (FK.openSub (fkRectCutGraph R) psi).Reachable
        (fkRectLeftColumn R, i) v ↔
      (FK.openSub (fkRectCutGraph R) rho).Reachable
        (fkRectLeftColumn R, i) v := by
  let source : R.Vertex := (fkRectLeftColumn R, i)
  let Gpsi := FK.openSub (fkRectCutGraph R) psi
  let Grho := FK.openSub (fkRectCutGraph R) rho
  have transfer : ∀ {x y : R.Vertex},
      FKRectPrimalFullExploredVertex R S psi x →
      (Gpsi.Adj x y ↔ Grho.Adj x y) := by
    intro x y hx
    have hnot : s(x, y) ∉ fkRectPrimalAdaptiveInsideEdges R S psi :=
      not_mem_fkRectPrimalFullUnexploredPairEdges_of_explored_left
        R S psi hx
    have heq := hagree s(x, y) hnot
    constructor
    · rintro ⟨hadj, hopen⟩
      exact ⟨hadj, heq.symm ▸ hopen⟩
    · rintro ⟨hadj, hopen⟩
      exact ⟨hadj, heq ▸ hopen⟩
  constructor
  · intro hreach
    let liftWalk : ∀ {x y : R.Vertex}, Gpsi.Walk x y →
        Gpsi.Reachable source x → Grho.Walk x y := by
      intro x y path
      induction path with
      | nil => intro _; exact SimpleGraph.Walk.nil
      | @cons x y z hxy path ih =>
          intro hsx
          exact SimpleGraph.Walk.cons
            ((transfer ⟨i, hi, hsx⟩).1 hxy)
            (ih (hsx.trans hxy.reachable))
    exact hreach.elim fun path =>
      ⟨liftWalk path (SimpleGraph.Reachable.refl source)⟩
  · intro hreach
    let liftWalk : ∀ {x y : R.Vertex}, Grho.Walk x y →
        Gpsi.Reachable source x → Gpsi.Walk x y := by
      intro x y path
      induction path with
      | nil => intro _; exact SimpleGraph.Walk.nil
      | @cons x y z hxy path ih =>
          intro hsx
          have hxyPsi := (transfer ⟨i, hi, hsx⟩).2 hxy
          exact SimpleGraph.Walk.cons hxyPsi
            (ih (hsx.trans hxyPsi.reachable))
    exact hreach.elim fun path =>
      ⟨liftWalk path (SimpleGraph.Reachable.refl source)⟩

theorem fkRectPrimalFullExploredVertex_agreesOff_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (psi rho : ConfigSpace (Sym2 R.Vertex))
    (hagree : FK.AgreesOff
      (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho)
    (v : R.Vertex) :
    FKRectPrimalFullExploredVertex R S psi v ↔
      FKRectPrimalFullExploredVertex R S rho v := by
  constructor
  · rintro ⟨i, hi, hiv⟩
    exact ⟨i, hi,
      (fkRectPrimalSourceReachable_agreesOff_iff
        R S psi rho hagree hi v).1 hiv⟩
  · rintro ⟨i, hi, hiv⟩
    exact ⟨i, hi,
      (fkRectPrimalSourceReachable_agreesOff_iff
        R S psi rho hagree hi v).2 hiv⟩

theorem fkRectPrimalAdaptiveInsideEdges_eq_of_agreesOff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (psi rho : ConfigSpace (Sym2 R.Vertex))
    (hagree : FK.AgreesOff
      (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho) :
    fkRectPrimalAdaptiveInsideEdges R S rho =
      fkRectPrimalAdaptiveInsideEdges R S psi := by
  unfold fkRectPrimalAdaptiveInsideEdges
  ext e
  rw [mem_fkRectPrimalFullUnexploredPairEdges_iff,
    mem_fkRectPrimalFullUnexploredPairEdges_iff]
  constructor
  · rintro ⟨x, y, he, hx, hy⟩
    exact ⟨x, y, he,
      fun h => hx ((fkRectPrimalFullExploredVertex_agreesOff_iff
        R S psi rho hagree x).1 h),
      fun h => hy ((fkRectPrimalFullExploredVertex_agreesOff_iff
        R S psi rho hagree y).1 h)⟩
  · rintro ⟨x, y, he, hx, hy⟩
    exact ⟨x, y, he,
      fun h => hx ((fkRectPrimalFullExploredVertex_agreesOff_iff
        R S psi rho hagree x).2 h),
      fun h => hy ((fkRectPrimalFullExploredVertex_agreesOff_iff
        R S psi rho hagree y).2 h)⟩


theorem fkRectPrimalAdaptiveProjection_filter_eq_condFibre
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (psi : ConfigSpace (Sym2 R.Vertex))
    (hpsi : fkRectPrimalAdaptiveProjection R S psi = psi) :
    Finset.univ.filter
        (fun rho => fkRectPrimalAdaptiveProjection R S rho = psi) =
      FK.condFibre (fkRectPrimalAdaptiveInsideEdges R S psi) psi := by
  ext rho
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, FK.mem_condFibre]
  constructor
  · intro hproj
    have hF : fkRectPrimalAdaptiveInsideEdges R S rho =
        fkRectPrimalAdaptiveInsideEdges R S psi := by
      rw [← fkRectPrimalAdaptiveInsideEdges_projection R S rho, hproj]
    intro e he
    have hval := congrFun hproj e
    have hnotRho : e ∉ fkRectPrimalAdaptiveInsideEdges R S rho := by
      rwa [hF]
    rw [← hval]
    exact (fkRectPrimalAdaptiveProjection_eq_of_not_mem
      R S rho hnotRho).symm
  · intro hagree
    have hF := fkRectPrimalAdaptiveInsideEdges_eq_of_agreesOff
      R S psi rho hagree
    unfold fkRectPrimalAdaptiveProjection
    rw [hF]
    have hproj := FK.projOff_eq_of_agreesOff hagree
    rw [hproj]
    simpa [fkRectPrimalAdaptiveProjection] using hpsi


end
end StatMech.FrontierD
