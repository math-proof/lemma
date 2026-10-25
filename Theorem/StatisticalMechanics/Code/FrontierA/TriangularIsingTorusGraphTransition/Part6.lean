/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorContinuation
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusGraphTransition.Part5


namespace StatMech.FrontierA

open SimpleGraph StatMech.Onsager

theorem kwGraphTransition_triangularTorusDartEquiv_apply
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho u v : Complex) (d e : triangularTorusDart L) :
    kwGraphTransition (triangularTorusGraph L)
        (triangularTorusEdgeWeight L t1 t2 t3)
        (triangularTorusGraphPhase L rho u v)
        (triangularTorusDartEquiv L d) (triangularTorusDartEquiv L e) =
      if (triangularTorusDartEquiv L d).snd =
            (triangularTorusDartEquiv L e).fst ∧
          (triangularTorusDartEquiv L d).edge ≠
            (triangularTorusDartEquiv L e).edge then
        triangularTorusDirectionWeight t1 t2 t3 d.2 *
          (triangularTorusDirectionPhase u v d.2 *
            triangularKacWardTurnMatrix rho d.2 e.2)
      else 0 := by
  unfold kwGraphTransition
  split
  · rw [triangularTorusEdgeWeight_dart]
    unfold triangularTorusGraphPhase
    dsimp only
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · rfl


theorem triangularTorusDartEquiv_consecutive_iff
    (L : Nat) [Fact (2 < L)] (d e : triangularTorusDart L) :
    (triangularTorusDartEquiv L d).snd =
        (triangularTorusDartEquiv L e).fst ↔
      (d.1.1 - e.1.1, d.1.2 - e.1.2) =
        triangularTorusDirectionStep L d.2 := by
  change d.1 - triangularTorusDirectionStep L d.2 = e.1 ↔
    d.1 - e.1 = triangularTorusDirectionStep L d.2
  constructor <;> intro h <;> rw [← h] <;> simp


theorem triangularTorusDartEquiv_edge_eq_iff_reverse
    (L : Nat) [Fact (2 < L)] (d e : triangularTorusDart L)
    (hc : (triangularTorusDartEquiv L d).snd =
      (triangularTorusDartEquiv L e).fst) :
    (triangularTorusDartEquiv L d).edge =
        (triangularTorusDartEquiv L e).edge ↔
      e = triangularTorusDartReverse L d := by
  constructor
  · intro hedge
    rcases (dart_edge_eq_iff
      (triangularTorusDartEquiv L d)
      (triangularTorusDartEquiv L e)).mp hedge with hsame | hsymm
    · exfalso
      apply (triangularTorusDartEquiv L d).fst_ne_snd
      calc
        (triangularTorusDartEquiv L d).fst =
            (triangularTorusDartEquiv L e).fst :=
          congrArg (fun z : (triangularTorusGraph L).Dart => z.fst) hsame
        _ = (triangularTorusDartEquiv L d).snd := hc.symm
    · apply (triangularTorusDartEquiv L).injective
      rw [triangularTorusDartEquiv_reverse]
      simpa using (congrArg Dart.symm hsymm).symm
  · rintro rfl
    rw [triangularTorusDartEquiv_reverse, Dart.edge_symm]


theorem triangularTorusKWMatrix_eq_reindex_graphTransition
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho u v : Complex) :
    triangularTorusKWMatrix L t1 t2 t3 rho u v =
      (Matrix.reindex (triangularTorusDartEquiv L).symm
        (triangularTorusDartEquiv L).symm)
        (kwGraphTransition (triangularTorusGraph L)
          (triangularTorusEdgeWeight L t1 t2 t3)
          (triangularTorusGraphPhase L rho u v)) := by
  ext d e
  rw [Matrix.reindex_apply]
  change triangularTorusKWMatrix L t1 t2 t3 rho u v d e =
    kwGraphTransition (triangularTorusGraph L)
      (triangularTorusEdgeWeight L t1 t2 t3)
      (triangularTorusGraphPhase L rho u v)
      (triangularTorusDartEquiv L d) (triangularTorusDartEquiv L e)
  rw [kwGraphTransition_triangularTorusDartEquiv_apply]
  unfold triangularTorusKWMatrix ons_blockCirculant2D
    triangularTorusKWBlock
  by_cases hs : (d.1.1 - e.1.1, d.1.2 - e.1.2) =
      triangularTorusDirectionStep L d.2
  · rw [if_pos hs]
    have hc := (triangularTorusDartEquiv_consecutive_iff L d e).mpr hs
    by_cases he : e = triangularTorusDartReverse L d
    · subst e
      have hedge := (triangularTorusDartEquiv_edge_eq_iff_reverse
        L d (triangularTorusDartReverse L d) hc).mpr rfl
      rw [if_neg (fun h => h.2 hedge)]
      rw [show (triangularTorusDartReverse L d).2 =
        triangularTorusDirectionReverse d.2 from rfl,
        triangularKacWardTurnMatrix_reverse_zero]
      ring
    · have hedge : (triangularTorusDartEquiv L d).edge ≠
          (triangularTorusDartEquiv L e).edge := by
        intro h
        exact he ((triangularTorusDartEquiv_edge_eq_iff_reverse
          L d e hc).mp h)
      rw [if_pos ⟨hc, hedge⟩]
      ring
  · rw [if_neg hs]
    have hc : ¬(triangularTorusDartEquiv L d).snd =
        (triangularTorusDartEquiv L e).fst := fun h =>
      hs ((triangularTorusDartEquiv_consecutive_iff L d e).mp h)
    rw [if_neg (fun h => hc h.1)]


theorem det_one_sub_triangularTorusKWMatrix_eq_graphTransition
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho u v : Complex) :
    (1 - triangularTorusKWMatrix L t1 t2 t3 rho u v).det =
      (1 - kwGraphTransition (triangularTorusGraph L)
        (triangularTorusEdgeWeight L t1 t2 t3)
        (triangularTorusGraphPhase L rho u v)).det := by
  rw [triangularTorusKWMatrix_eq_reindex_graphTransition]
  let e := (triangularTorusDartEquiv L).symm
  let M := kwGraphTransition (triangularTorusGraph L)
    (triangularTorusEdgeWeight L t1 t2 t3)
    (triangularTorusGraphPhase L rho u v)
  have hsub : 1 - Matrix.reindex e e M =
      Matrix.reindex e e (1 - M) := by
    ext d f
    simp [Matrix.reindex_apply, Matrix.one_apply]
  rw [hsub, Matrix.det_reindex_self]

end StatMech.FrontierA
