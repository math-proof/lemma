/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc17menger.Part4
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Def.StatisticalMechanics.Code.Walls.bc18mengerhard.Part2


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V]

variable {G : SimpleGraph V}


theorem bc18_reachableRestrCompl_to_walk {Y : Set V} {a b : V} (ha : a ∉ Y)
    (h : (bc17_restr G {v | v ∉ Y}).Reachable a b) :
    ∃ p : G.Walk a b, ∀ w ∈ p.support, w ∉ Y := by
  obtain ⟨q⟩ := h
  refine ⟨q.mapLe (bc17_restr_le G _), ?_⟩
  intro w hw
  rw [Walk.support_mapLe_eq_support] at hw
  exact bc17_restr_support_subset G _ ha q w hw


theorem bc18_restr_compl_deleteEdges {Y : Set V} {x y : V} :
    (bc17_restr G {v | v ∉ Y}).deleteEdges {s(x, y)}
      = bc17_restr (G.deleteEdges {s(x, y)}) {v | v ∉ Y} := by
  ext u v
  simp only [deleteEdges_adj, bc17_restr_adj, Set.mem_singleton_iff]
  tauto


theorem bc18_areach_to_reachable_del {A Y : Set V} {c x y z : V}
    (hz : z ∈ bc18_AReach G A (insert c Y)) (hzS : z ∉ insert c Y)
    (hc : c = x ∨ c = y) :
    ∃ a ∈ A, a ∉ Y ∧
      (bc17_restr (G.deleteEdges {s(x, y)}) {v | v ∉ Y}).Reachable a z := by
  obtain ⟨a, ha, p, hp⟩ := hz
  have hpavoid : ∀ w ∈ p.support, w ∉ insert c Y := by
    intro w hw hwS; exact hzS ((hp w hw hwS) ▸ hwS)
  have hpY : ∀ w ∈ p.support, w ∉ Y := fun w hw hwY => hpavoid w hw (Set.mem_insert_of_mem _ hwY)
  have hpc : ∀ w ∈ p.support, w ≠ c := fun w hw h => hpavoid w hw (h ▸ Set.mem_insert _ _)
  have hedge : s(x, y) ∉ p.edges := by
    intro he; rcases hc with hcx | hcy
    · exact hpc x (p.fst_mem_support_of_mem_edges he) hcx.symm
    · exact hpc y (p.snd_mem_support_of_mem_edges he) hcy.symm
  refine ⟨a, ha, hpY a p.start_mem_support,
    ⟨bc18_walkToRestrCompl (p.toDeleteEdge (s(x, y)) hedge) ?_⟩⟩
  intro w hw
  rw [Walk.support_transfer] at hw
  exact hpY w hw


theorem bc18_contra_of_reachable {A B Y : Set V} {x y a b : V}
    (hYsep : bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y)
    (ha : a ∈ A) (hb : b ∈ B) (haY : a ∉ Y)
    (h : (bc17_restr (G.deleteEdges {s(x, y)}) {v | v ∉ Y}).Reachable a b) : False := by
  obtain ⟨p, hp⟩ := bc18_reachableRestrCompl_to_walk haY h
  obtain ⟨cc, hccY, hccp⟩ := hYsep ha hb p
  exact hp cc hccp hccY


theorem bc18_notBoth {A B Y : Set V} {x y : V}
    (hxy : G.Adj x y) (hxY : x ∉ Y) (hyY : y ∉ Y)
    (hYsep : bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y)
    (hYnotG : ¬ bc16_IsSeparator G A B Y) :
    ¬ (y ∈ bc18_AReach G A (insert x Y) ∧ x ∈ bc18_AReach G A (insert y Y)) := by
  rintro ⟨hyA, hxA⟩
  rw [bc16_IsSeparator] at hYnotG
  push Not at hYnotG
  obtain ⟨a₀, ha₀, b₀, hb₀, R₀, hR₀⟩ := hYnotG
  have ha₀Y : a₀ ∉ Y := fun h => hR₀ a₀ h R₀.start_mem_support
  have hne : x ≠ y := hxy.ne
  have hy_notin : y ∉ insert x Y := by simp [Set.mem_insert_iff, hne.symm, hyY]
  have hx_notin : x ∉ insert y Y := by simp [Set.mem_insert_iff, hne, hxY]
  obtain ⟨ay, hayA, hayY, hayreach⟩ :=
    bc18_areach_to_reachable_del (c := x) (x := x) (y := y) (z := y) hyA hy_notin (Or.inl rfl)
  obtain ⟨ax, haxA, haxY, haxreach⟩ :=
    bc18_areach_to_reachable_del (c := y) (x := x) (y := y) (z := x) hxA hx_notin (Or.inr rfl)
  have hR₀restr : (bc17_restr G {v | v ∉ Y}).Reachable a₀ b₀ :=
    ⟨bc18_walkToRestrCompl R₀ (fun w hw hwY => hR₀ w hwY hw)⟩
  rcases hR₀restr with ⟨R₀'⟩
  rcases bc18_splitAtEdge (x := x) (y := y) R₀' with hkeep | ⟨_, h2⟩ | ⟨_, h2⟩
  · rw [bc18_restr_compl_deleteEdges] at hkeep
    exact bc18_contra_of_reachable hYsep ha₀ hb₀ ha₀Y hkeep
  · rw [bc18_restr_compl_deleteEdges] at h2
    exact bc18_contra_of_reachable hYsep hayA hb₀ hayY (hayreach.trans h2)
  · rw [bc18_restr_compl_deleteEdges] at h2
    exact bc18_contra_of_reachable hYsep haxA hb₀ haxY (haxreach.trans h2)


theorem bc18_AReach_inter_subset {A B S : Set V} (hS : bc16_IsSeparator G A B S) :
    bc18_AReach G A S ∩ bc18_AReach G B S ⊆ S := by
  rintro z ⟨⟨a, ha, pa, hpa⟩, ⟨b, hb, pb, hpb⟩⟩
  by_contra hzS
  have hpaS : ∀ w ∈ pa.support, w ∉ S := fun w hw hwS => hzS ((hpa w hw hwS) ▸ hwS)
  have hpbS : ∀ w ∈ pb.support, w ∉ S := fun w hw hwS => hzS ((hpb w hw hwS) ▸ hwS)
  obtain ⟨cc, hccS, hccp⟩ := hS ha hb (pa.append pb.reverse)
  rw [Walk.mem_support_append_iff] at hccp
  rcases hccp with h | h
  · exact hpaS cc h hccS
  · rw [Walk.support_reverse, List.mem_reverse] at h
    exact hpbS cc h hccS


theorem bc18_mem_AReach_of_essential {A B S : Set V} {w : V}
    (hSsep : bc16_IsSeparator G A B S)
    (hnotSep : ¬ bc16_IsSeparator G A B (S \ {w})) :
    w ∈ bc18_AReach G A S := by
  rw [bc16_IsSeparator] at hnotSep
  push Not at hnotSep
  obtain ⟨a, ha, b, hb, R, hR⟩ := hnotSep
  obtain ⟨c, hcS, hcR⟩ := hSsep ha hb R
  have hcw : c = w := by
    by_contra hcw; exact hR c ⟨hcS, hcw⟩ hcR
  obtain ⟨c', q, hqpath, hc'S, hqsub, hq⟩ := bc18_firstHitPath R ⟨c, hcR, hcS⟩
  have hc'w : c' = w := by
    have hc'R : c' ∈ R.support := hqsub (Walk.end_mem_support q)
    by_contra hh; exact hR c' ⟨hc'S, hh⟩ hc'R
  rw [← hc'w]
  exact ⟨a, ha, q, hq⟩


theorem bc18_appendPath_of_inter {a v b : V} {p : G.Walk a v} {q : G.Walk v b}
    (hp : p.IsPath) (hq : q.IsPath)
    (hint : ∀ z, z ∈ p.support → z ∈ q.support → z = v) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  refine ⟨hp.support_nodup, (hq.support_nodup).tail, ?_⟩
  intro z hz w hw heq
  subst heq
  have hzq : z ∈ q.support := List.mem_of_mem_tail hw
  have hzv : z = v := hint z hz hzq
  subst hzv
  have hnd : (z :: q.support.tail).Nodup := by
    rw [Walk.cons_tail_support]; exact hq.support_nodup
  exact (List.nodup_cons.mp hnd).1 hw


theorem bc18_aside_fan {A B S : Set V} {k : ℕ}
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
    (hSsep : bc16_IsSeparator G A B S)
    (hH : bc17_HardDir (bc17_restr G (bc18_AReach G A S)) A S) :
    Nonempty (bc16_DisjointPathFamily (bc17_restr G (bc18_AReach G A S)) A S (Fin k)) := by
  refine hH k (fun C hC => hmin C ?_)
  exact bc18_AReach_separator_transfer hSsep hC

end StatMech.Walls
