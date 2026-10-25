/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part9


namespace StatMech.FrontierD

noncomputable section

theorem FKRectSquareAxisStep.symm {p q : Int × Int}
    (h : FKRectSquareAxisStep p q) :
    FKRectSquareAxisStep q p := by
  rcases h with h | h | h | h
  · right; right; left
    apply Prod.ext <;>
      have := congrArg (fun z : Int × Int => z.1) h <;>
      have := congrArg (fun z : Int × Int => z.2) h <;>
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at * <;>
      omega
  · right; right; right
    apply Prod.ext <;>
      have := congrArg (fun z : Int × Int => z.1) h <;>
      have := congrArg (fun z : Int × Int => z.2) h <;>
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at * <;>
      omega
  · left
    apply Prod.ext <;>
      have := congrArg (fun z : Int × Int => z.1) h <;>
      have := congrArg (fun z : Int × Int => z.2) h <;>
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at * <;>
      omega
  · right; left
    apply Prod.ext <;>
      have := congrArg (fun z : Int × Int => z.1) h <;>
      have := congrArg (fun z : Int × Int => z.2) h <;>
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at * <;>
      omega


theorem fkRectSquareDevelopPoint_sub_add_period
    (R : FKRectTorus) (p q u : Int × Int) :
    fkRectSquareDevelopPoint
          (q.1 + (R.width : Int) * u.1,
            q.2 + (R.height : Int) * u.2) -
        fkRectSquareDevelopPoint
          (p.1 + (R.width : Int) * u.1,
            p.2 + (R.height : Int) * u.2) =
      fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p := by
  have hp := fkRectSquareDevelopPoint_add_period R p u
  have hq := fkRectSquareDevelopPoint_add_period R q u
  apply Prod.ext
  · have hp' := congrArg Prod.fst hp
    have hq' := congrArg Prod.fst hq
    simp only [Prod.fst_sub] at hp' hq' ⊢
    omega
  · have hp' := congrArg Prod.snd hp
    have hq' := congrArg Prod.snd hq
    simp only [Prod.snd_sub] at hp' hq' ⊢
    omega


theorem fkRectTorusGraph_adj_squareLift
    (R : FKRectTorus) {x y : R.Vertex}
    (hxy : (fkRectTorusGraph R).Adj x y)
    (p : Int × Int) (hp : fkRectLiftedVertex R p = x) :
    ∃ q : Int × Int,
      fkRectLiftedVertex R q = y ∧
        q - p = fkRectDevelopedStep R x y ∧
        FKRectSquareAxisStep (fkRectSquareDevelopPoint p)
          (fkRectSquareDevelopPoint q) := by
  obtain ⟨e, he⟩ := hxy
  obtain ⟨a, b, hedge, ha, hb, hdeveloped, hstep⟩ :=
    fkRectIndexedEdge_squareLift R e
  have hpairs :
      s(fkRectLiftedVertex R a, fkRectLiftedVertex R b) = s(x, y) :=
    hedge.symm.trans he
  rcases Sym2.eq_iff.mp hpairs with horient | horient
  · have hpa : fkRectLiftedVertex R p = fkRectLiftedVertex R a :=
      hp.trans horient.1.symm
    obtain ⟨u, hu⟩ :=
      (fkRectLiftedVertex_eq_iff_exists_period R p a).mp hpa
    let q : Int × Int :=
      (b.1 + (R.width : Int) * u.1,
        b.2 + (R.height : Int) * u.2)
    refine ⟨q, ?_, ?_, ?_⟩
    · have hqb : fkRectLiftedVertex R q = fkRectLiftedVertex R b :=
        (fkRectLiftedVertex_eq_iff_exists_period R q b).mpr ⟨u, rfl⟩
      exact hqb.trans horient.2
    · rw [← horient.1, ← horient.2, hdeveloped]
      dsimp [q]
      rw [hu]
      apply Prod.ext <;> simp <;> ring
    · rw [hu]
      dsimp [q]
      unfold FKRectSquareAxisStep
      rw [fkRectSquareDevelopPoint_sub_add_period R a b u]
      exact hstep.elim Or.inl (fun h => Or.inr (Or.inl h))
  · have hpb : fkRectLiftedVertex R p = fkRectLiftedVertex R b :=
      hp.trans horient.2.symm
    obtain ⟨u, hu⟩ :=
      (fkRectLiftedVertex_eq_iff_exists_period R p b).mp hpb
    let q : Int × Int :=
      (a.1 + (R.width : Int) * u.1,
        a.2 + (R.height : Int) * u.2)
    refine ⟨q, ?_, ?_, ?_⟩
    · have hqa : fkRectLiftedVertex R q = fkRectLiftedVertex R a :=
        (fkRectLiftedVertex_eq_iff_exists_period R q a).mpr ⟨u, rfl⟩
      exact hqa.trans horient.1
    · rw [← horient.2, ← horient.1,
        fkRectDevelopedStep_swap, hdeveloped]
      dsimp [q]
      rw [hu]
      apply Prod.ext <;> simp <;> ring
    · rw [hu]
      dsimp [q]
      apply FKRectSquareAxisStep.symm
      unfold FKRectSquareAxisStep
      rw [fkRectSquareDevelopPoint_sub_add_period R a b u]
      exact hstep.elim Or.inl (fun h => Or.inr (Or.inl h))


end
end StatMech.FrontierD
