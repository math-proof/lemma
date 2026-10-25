/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part35


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredTransitionTurn_completedIncidence
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredTransitionTurn n hn omega x
      (fkIsingSquareWiredCompletedIncidenceEquiv n x) = 0 := by
  cases x <;> simp [fkIsingSquareWiredCompletedIncidenceEquiv,
    fkIsingSquareWiredTransitionTurn]

theorem fkIsingSquareWiredCarrierMacroVertexWord_nodup
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredCarrierMacroVertexWord n hn omega d).Nodup := by
  simp [fkIsingSquareWiredCarrierMacroVertexWord]
  exact (fkIsingSquareWiredTransitionMate_ne n hn omega _).symm

theorem fkIsingSquareWiredCarrierMacroVertexWord_disjoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d e : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hne : d ≠ e) :
    List.Disjoint
      (fkIsingSquareWiredCarrierMacroVertexWord n hn omega d)
      (fkIsingSquareWiredCarrierMacroVertexWord n hn omega e) := by
  apply List.disjoint_left.2
  intro z hzd hze
  simp only [fkIsingSquareWiredCarrierMacroVertexWord,
    List.mem_cons, List.not_mem_nil, or_false] at hzd hze
  rcases hzd with hzd | hzd <;> rcases hze with hze | hze
  · exact hne (fkIsingSquareWiredBlackOfDart_injective n
      (Subtype.ext (hzd.symm.trans hze)))
  · have hc := fkIsingSquareWiredCarrierColor_transition_ne n hn omega
      (fkIsingSquareWiredBlackOfDart n e).1
    change fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredTransitionMate n hn omega
          (fkIsingSquareWiredBlackOfDart n e).1) ≠
      fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredBlackOfDart n e).1 at hc
    rw [← hze, hzd] at hc
    exact hc ((fkIsingSquareWiredBlackOfDart n d).2.trans
      (fkIsingSquareWiredBlackOfDart n e).2.symm)
  · have hc := fkIsingSquareWiredCarrierColor_transition_ne n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1
    change fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredTransitionMate n hn omega
          (fkIsingSquareWiredBlackOfDart n d).1) ≠
      fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredBlackOfDart n d).1 at hc
    rw [← hzd, hze] at hc
    exact hc ((fkIsingSquareWiredBlackOfDart n e).2.trans
      (fkIsingSquareWiredBlackOfDart n d).2.symm)
  · have hb : (fkIsingSquareWiredBlackOfDart n d).1 =
        (fkIsingSquareWiredBlackOfDart n e).1 := by
      apply (fkIsingSquareWiredTransitionMate_involutive n hn omega).injective
      exact hzd.symm.trans hze
    exact hne (fkIsingSquareWiredBlackOfDart_injective n (Subtype.ext hb))


theorem fkIsingSquareWiredCompletedGraph_exists_portNext_carrier_path
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    ∃ p : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Walk
        (fkIsingSquareWiredBlackOfDart n d).1
        (fkIsingSquareWiredBlackOfDart n
          (fkIsingSquareWiredPortNext n hn omega d)).1,
      p.IsPath ∧
      p.support = fkIsingSquareWiredCarrierMacroVertexWord n hn omega d ++
        [(fkIsingSquareWiredBlackOfDart n
          (fkIsingSquareWiredPortNext n hn omega d)).1] ∧
      carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
          p.support =
        fkIsingSquareWiredTransitionTurn n hn omega
          (fkIsingSquareWiredBlackOfDart n d).1
          (fkIsingSquareWiredTransitionMate n hn omega
            (fkIsingSquareWiredBlackOfDart n d).1) := by
  let b := (fkIsingSquareWiredBlackOfDart n d).1
  let t := fkIsingSquareWiredTransitionMate n hn omega b
  let bn := (fkIsingSquareWiredBlackOfDart n
    (fkIsingSquareWiredPortNext n hn omega d)).1
  have hstep := fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
    n hn omega d hsource hterminal
  have hvalue := congrArg (fun z : FKIsingSquareWiredBlackCarrier n => z.1) hstep
  have hboundary : fkIsingSquareWiredBoundaryStep n hn omega b = bn := by
    simpa [b, bn] using hvalue
  have hbt : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj b t :=
    (fkIsingSquareWiredCompletedLoopGraph_adj_iff n hn omega b t).mpr
      (Or.inl rfl)
  have htbn : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj t bn :=
    (fkIsingSquareWiredCompletedLoopGraph_adj_iff n hn omega t bn).mpr
      (Or.inr (by simpa [fkIsingSquareWiredBoundaryStep,
        Equiv.trans_apply, t] using hboundary.symm))
  let p := SimpleGraph.Walk.cons hbt
    (SimpleGraph.Walk.cons htbn SimpleGraph.Walk.nil)
  refine ⟨p, ?_, ?_, ?_⟩
  · simp [p, SimpleGraph.Walk.isPath_def]
    constructor
    · constructor
      · exact (fkIsingSquareWiredTransitionMate_ne n hn omega b).symm
      · have hne := fkIsingSquareWiredPortNext_ne n hn omega d
        exact fun h => hne (fkIsingSquareWiredBlackOfDart_injective n
          (Subtype.ext h.symm))
    · intro h
      have hc := fkIsingSquareWiredCarrierColor_transition_ne n hn omega b
      change fkIsingSquareWiredCarrierColor n t ≠
        fkIsingSquareWiredCarrierColor n b at hc
      rw [h] at hc
      exact hc ((fkIsingSquareWiredBlackOfDart n
        (fkIsingSquareWiredPortNext n hn omega d)).2.trans
        (fkIsingSquareWiredBlackOfDart n d).2.symm)
  · simp [p, fkIsingSquareWiredCarrierMacroVertexWord, b, t, bn]
  · have hincidence : fkIsingSquareWiredCompletedIncidenceEquiv n t = bn := by
      simpa [fkIsingSquareWiredBoundaryStep, Equiv.trans_apply, t]
        using hboundary
    have hsecond : fkIsingSquareWiredTransitionTurn n hn omega t bn = 0 := by
      rw [← hincidence]
      exact fkIsingSquareWiredTransitionTurn_completedIncidence n hn omega t
    simp [p, carrierAdjacentSum, b, t, bn, hsecond]

theorem carrierAdjacentSum_append_tail_eq_add
    {A : Type*} (g : A → A → Int) (l r : List A)
    (hl : l ≠ []) (hr : r ≠ [])
    (hjoin : l.getLast hl = r.head hr) :
    carrierAdjacentSum g (l ++ r.tail) =
      carrierAdjacentSum g l + carrierAdjacentSum g r := by
  cases r with
  | nil => exact False.elim (hr rfl)
  | cons a tail =>
      cases tail with
      | nil => simp
      | cons b tail =>
          have htail : b :: tail ≠ [] := by simp
          change carrierAdjacentSum g (l ++ b :: tail) =
            carrierAdjacentSum g l + carrierAdjacentSum g (a :: b :: tail)
          rw [carrierAdjacentSum_append g l (b :: tail) hl htail]
          simp only [List.tail_cons, carrierAdjacentSum_cons_cons]
          have hab : l.getLast hl = a := by simpa using hjoin
          have hbhead : (b :: tail).head htail = b := by simp
          rw [hab, hbhead]
          omega

theorem fkIsingSquareWiredCompletedGraph_exists_portNext_iterate_carrier_walk
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (k : Nat)
    (hsource : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredSourceDart n hn)
    (hterminal : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredTerminalDart n hn) :
    ∃ p : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Walk
        (fkIsingSquareWiredBlackOfDart n d).1
        (fkIsingSquareWiredBlackOfDart n
          ((fkIsingSquareWiredPortNext n hn omega)^[k] d)).1,
      let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k
      p.support = darts.flatMap
          (fkIsingSquareWiredCarrierMacroVertexWord n hn omega) ++
        [(fkIsingSquareWiredBlackOfDart n
          ((fkIsingSquareWiredPortNext n hn omega)^[k] d)).1] ∧
      carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
          p.support =
        (darts.map fun q => fkIsingSquareWiredTransitionTurn n hn omega
          (fkIsingSquareWiredBlackOfDart n q).1
          (fkIsingSquareWiredTransitionMate n hn omega
            (fkIsingSquareWiredBlackOfDart n q).1)).sum := by
  let f := fkIsingSquareWiredPortNext n hn omega
  induction k generalizing d with
  | zero => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ k ih =>
      obtain ⟨p, hpPath, hp, hpTurn⟩ :=
        fkIsingSquareWiredCompletedGraph_exists_portNext_carrier_path
          n hn omega d (hsource 0 (by omega)) (hterminal 0 (by omega))
      obtain ⟨q, hq, hqTurn⟩ := ih (f d)
        (fun i hi => by
          simpa [f, Function.iterate_succ_apply] using hsource (i + 1) (by omega))
        (fun i hi => by
          simpa [f, Function.iterate_succ_apply] using hterminal (i + 1) (by omega))
      let r := p.append q
      have hend : f^[k] (f d) = f^[k + 1] d := by
        simpa only [Function.iterate_succ_apply] using
          (Function.Commute.iterate_right (Function.Commute.refl f) k d)
      have hendCarrier : (fkIsingSquareWiredBlackOfDart n
          (f^[k] (f d))).1 =
          (fkIsingSquareWiredBlackOfDart n (f^[k + 1] d)).1 :=
        congrArg (fun z => (fkIsingSquareWiredBlackOfDart n z).1) hend
      let s := r.copy rfl hendCarrier
      refine ⟨s, ?_, ?_⟩
      · have hqCons := q.cons_tail_support
        rw [hq] at hqCons
        simp only [SimpleGraph.Walk.support_copy,
          SimpleGraph.Walk.support_append, s, r]
        rw [hp, hq]
        simp [List.iterate,
          fkIsingSquareWiredCarrierMacroVertexWord, hend]
        simpa only [f] using hqCons
      · have hpNe : p.support ≠ [] := SimpleGraph.Walk.support_ne_nil p
        have hqNe : q.support ≠ [] := SimpleGraph.Walk.support_ne_nil q
        have hjoin : p.support.getLast hpNe = q.support.head hqNe := by
          calc
            p.support.getLast hpNe =
                (fkIsingSquareWiredBlackOfDart n (f d)).1 := by
              simpa only [f] using SimpleGraph.Walk.getLast_support p
            _ = q.support.head hqNe := by
              simpa only [f] using (SimpleGraph.Walk.head_support q).symm
        calc
          carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
              s.support =
              carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
                (p.support ++ q.support.tail) := by
                exact congrArg
                  (carrierAdjacentSum
                    (fkIsingSquareWiredTransitionTurn n hn omega))
                  (by simpa only [s, SimpleGraph.Walk.support_copy, r] using
                    SimpleGraph.Walk.support_append p q)
          _ = carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
                p.support +
              carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
                q.support :=
            carrierAdjacentSum_append_tail_eq_add _ _ _ hpNe hqNe hjoin
          _ = _ := by
            rw [hpTurn, hqTurn]
            change _ +
                (List.map _ (List.iterate f (f d) k)).sum =
              (List.map _ (List.iterate f d (k + 1))).sum
            rw [show k + 1 = Nat.succ k by omega, List.iterate]
            simp

theorem fkIsingSquareWiredCompletedLoopGraph_isCycles
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).IsCycles := by
  intro v _
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
    SimpleGraph.card_neighborSet_eq_degree]
  simpa only using
    fkIsingSquareWiredCompletedLoopGraph_degree_eq_two n hn omega v


theorem fkIsingSquareWiredCompletedGraph_exists_carrier_cycle_of_local_black_orbit
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source) :
    let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
    let k := (sigma.cycleOf (fkIsingSquareWiredBlackOfDart n d)).support.card
    let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k
    ∃ p : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Walk
        (fkIsingSquareWiredBlackOfDart n d).1
        (fkIsingSquareWiredBlackOfDart n d).1,
      p.IsCycle ∧
      p.snd = fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1 ∧
      carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
          p.support =
        (darts.map fun q => fkIsingSquareWiredTransitionTurn n hn omega
          (fkIsingSquareWiredBlackOfDart n q).1
          (fkIsingSquareWiredTransitionMate n hn omega
            (fkIsingSquareWiredBlackOfDart n q).1)).sum := by
  dsimp only
  let f := fkIsingSquareWiredPortNext n hn omega
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
  let x := fkIsingSquareWiredBlackOfDart n d
  let k := (sigma.cycleOf x).support.card
  let darts := List.iterate f d k
  let block := fkIsingSquareWiredCarrierMacroVertexWord n hn omega
  have havoid :=
    fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source
      n hn omega d hroot
  have hstep := fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
    n hn omega d (havoid 0).1 (havoid 0).2
  have hmove : sigma x ≠ x := by
    intro heq
    change sigma x = fkIsingSquareWiredBlackOfDart n (f d) at hstep
    rw [heq] at hstep
    exact fkIsingSquareWiredPortNext_ne n hn omega d
      (fkIsingSquareWiredBlackOfDart_injective n hstep.symm)
  have hxmem : x ∈ sigma.support := Equiv.Perm.mem_support.mpr hmove
  have hkTwo : 2 ≤ k := by
    change 2 ≤ (sigma.cycleOf x).support.card
    rw [← Equiv.Perm.length_toList sigma x]
    exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hxmem
  have hxCycle : x ∈ (sigma.cycleOf x).support := by
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    exact ⟨Equiv.Perm.SameCycle.rfl, hxmem⟩
  have hpermClose : (sigma ^ k) x = x := by
    have hmod := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply sigma k x
    simpa [k] using hmod.symm
  have hconj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
    n hn omega d k (fun i _ => (havoid i).1) (fun i _ => (havoid i).2)
  change (sigma ^ k) x = fkIsingSquareWiredBlackOfDart n (f^[k] d) at hconj
  have hclose : f^[k] d = d :=
    fkIsingSquareWiredBlackOfDart_injective n
      (hconj.symm.trans hpermClose)
  have hdartsNodup : darts.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro i j hij
    have hij' : f^[i.1] d = f^[j.1] d := by
      simpa [darts, List.getElem_iterate] using hij
    have hiConj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
      n hn omega d i.1 (fun q _ => (havoid q).1) (fun q _ => (havoid q).2)
    have hjConj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
      n hn omega d j.1 (fun q _ => (havoid q).1) (fun q _ => (havoid q).2)
    change (sigma ^ i.1) x = fkIsingSquareWiredBlackOfDart n (f^[i.1] d)
      at hiConj
    change (sigma ^ j.1) x = fkIsingSquareWiredBlackOfDart n (f^[j.1] d)
      at hjConj
    have hpows : (sigma ^ i.1) x = (sigma ^ j.1) x := by
      rw [hiConj, hjConj, hij']
    have hcycleOn := Equiv.Perm.isCycleOn_support_cycleOf sigma x
    have hmod := (hcycleOn.pow_apply_eq_pow_apply hxCycle).mp hpows
    change i.1 % k = j.1 % k at hmod
    rw [Nat.mod_eq_of_lt (by simpa [darts] using i.isLt),
      Nat.mod_eq_of_lt (by simpa [darts] using j.isLt)] at hmod
    exact Fin.ext hmod
  have hverticesNodup : (darts.flatMap block).Nodup := by
    rw [List.nodup_flatMap]
    constructor
    · intro q _
      exact fkIsingSquareWiredCarrierMacroVertexWord_nodup n hn omega q
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      apply fkIsingSquareWiredCarrierMacroVertexWord_disjoint n hn omega
      intro heq
      exact (Nat.ne_of_lt hij) (hdartsNodup.getElem_inj_iff.mp heq)
  obtain ⟨r, hrSupport, hrTurn⟩ :=
    fkIsingSquareWiredCompletedGraph_exists_portNext_iterate_carrier_walk
      n hn omega d k (fun i _ => (havoid i).1) (fun i _ => (havoid i).2)
  let p : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Walk x.1 x.1 :=
    r.copy rfl (congrArg (fun z =>
      (fkIsingSquareWiredBlackOfDart n z).1) hclose)
  have hpSupport : p.support = darts.flatMap block ++ [x.1] := by
    simpa [p, darts, block, x, f, hclose] using hrSupport
  have hpTurn : carrierAdjacentSum
      (fkIsingSquareWiredTransitionTurn n hn omega) p.support =
      (darts.map fun q => fkIsingSquareWiredTransitionTurn n hn omega
        (fkIsingSquareWiredBlackOfDart n q).1
        (fkIsingSquareWiredTransitionMate n hn omega
          (fkIsingSquareWiredBlackOfDart n q).1)).sum := by
    simpa [p, darts, f] using hrTurn
  have hverticesNe : darts.flatMap block ≠ [] := by
    exact List.flatMap_ne_nil_of_ne_nil block
      (fun q => by simp [block, fkIsingSquareWiredCarrierMacroVertexWord])
      darts (by simp [darts]; omega)
  have hheadVertices : (darts.flatMap block).head hverticesNe = x.1 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp [darts, block, x, hm, fkIsingSquareWiredCarrierMacroVertexWord]
  have htailNodup : p.support.tail.Nodup := by
    obtain ⟨a, tail, hvertices⟩ := List.exists_cons_of_ne_nil hverticesNe
    have ha : a = x.1 := by simpa [hvertices] using hheadVertices
    subst a
    rw [hpSupport, hvertices]
    simp only [List.cons_append, List.tail_cons]
    rw [List.nodup_append]
    have hv := hverticesNodup
    rw [hvertices, List.nodup_cons] at hv
    refine ⟨hv.2, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    apply hv.1
    rw [← hb, ← hab]
    exact ha
  have hpLength : 2 < p.length := by
    have hlen := p.length_support
    rw [hpSupport] at hlen
    simp [darts, block, fkIsingSquareWiredCarrierMacroVertexWord] at hlen
    omega
  have hpNotNil : p ≠ SimpleGraph.Walk.nil := by
    intro h
    have hlen : p.length = 0 := by
      simpa using congrArg SimpleGraph.Walk.length h
    omega
  have hpNotNilPred : ¬p.Nil := fun hnil => hpNotNil hnil.eq_nil
  have htailPath : p.tail.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    rw [p.support_tail_of_not_nil hpNotNilPred]
    exact htailNodup)
  have hpCycle : p.IsCycle := by
    exact SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      ⟨htailPath, by omega⟩
  have hpSnd : p.snd = fkIsingSquareWiredTransitionMate n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1 := by
    have hsnd := p.snd_eq_support_getElem_one hpNotNilPred
    have h1 : 1 < p.support.length := by
      rw [p.length_support]
      omega
    have hsndOpt : p.support[1]? = some p.snd := by
      rw [List.getElem?_eq_getElem h1, ← hsnd]
    have hsupportOpt := congrArg (fun l => l[1]?) hpSupport
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have htarget : p.support[1]? = some
        (fkIsingSquareWiredTransitionMate n hn omega
          (fkIsingSquareWiredBlackOfDart n d).1) := by
      simpa [darts, block, x, hm,
        fkIsingSquareWiredCarrierMacroVertexWord] using hsupportOpt
    exact Option.some_inj.mp (hsndOpt.symm.trans htarget)
  exact ⟨p, hpCycle, hpSnd, hpTurn⟩

theorem fkIsingSquareWired_carrierAdjacentSum_open_eq_closed_of_deleted_local
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    {a b : FKIsingSquareWiredCarrier n}
    (r : ((fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).deleteEdges
        {s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)),
          s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east))}).Walk
            a b) :
    carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support =
      carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)) r.support := by
  apply carrierAdjacentSum_chain_congr
  exact r.isChain_adj_support.imp (by
    intro x y hxy
    apply fkIsingSquareWiredTransitionTurn_open_eq_closed_of_nonlocal
    intro side hx side' hy
    subst x
    subst y
    cases side <;> cases side' <;>
      simp [SimpleGraph.deleteEdges_adj,
        fkIsingSquareWiredLoopGraph,
        fkIsingSquareWiredTransitionMate,
        fkIsingSquareWiredIncidenceMate,
        FKIsingMedialDart.localMate, setClosed] at hxy)

theorem fkIsingSquareWired_carrierAdjacentSum_open_eq_closed_of_deleted_local_comm
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    {a b : FKIsingSquareWiredCarrier n}
    (r : ((fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).deleteEdges
        {s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)),
          s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west))}).Walk
            a b) :
    carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support =
      carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)) r.support := by
  apply carrierAdjacentSum_chain_congr
  exact r.isChain_adj_support.imp (by
    intro x y hxy
    apply fkIsingSquareWiredTransitionTurn_open_eq_closed_of_nonlocal
    intro side hx side' hy
    subst x
    subst y
    cases side <;> cases side' <;>
      simp [SimpleGraph.deleteEdges_adj,
        fkIsingSquareWiredLoopGraph,
        fkIsingSquareWiredTransitionMate,
        fkIsingSquareWiredIncidenceMate,
        FKIsingMedialDart.localMate, setClosed] at hxy)


theorem fkIsingSquareWired_one_visit_west_cycle_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (r : ((fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).deleteEdges
        {s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)),
          s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east))}).Walk
            (.dart (e, .east)) (.dart (e, .north)))
    (hr : r.IsPath) :
    carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support +
      fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
        (.dart (e, .north)) (.dart (e, .east)) ≡ 8 [ZMOD 16] := by
  let closed := setClosed e.1 omega
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .east)
  have hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn closed).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source := by
    intro hreach
    apply heast
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    simpa only [closed, d, fkIsingSquareWiredBlackOfDart] using hreach.symm
  obtain ⟨c, hc, hcSnd, hcTurn⟩ :=
    fkIsingSquareWiredCompletedGraph_exists_carrier_cycle_of_local_black_orbit
      n hn closed d hroot
  have hcMod := fkIsingSquareWired_local_black_orbit_transition_turn_mod_sixteen
    n hn closed d hroot
  dsimp only at hcMod
  rw [← hcTurn] at hcMod
  obtain ⟨q, hq, hqSupport⟩ :=
    fkIsingSquareWired_one_visit_west_carrierCycle
      n hn omega e r hr
  let qC := q.mapLe (show fkIsingSquareWiredLoopGraph n hn closed ≤
      fkIsingSquareWiredCompletedLoopGraph n hn closed from le_sup_left)
  have hqC : qC.IsCycle := hq.mapLe _
  have hqCSupport : qC.support = E :: r.reverse.support := by
    calc
      qC.support = q.support := by
        exact SimpleGraph.Walk.support_mapLe_eq_support _ q
      _ = E :: r.reverse.support := by simpa [E] using hqSupport
  have hqCSnd : qC.snd = N := by
    have hsnd := qC.snd_eq_support_getElem_one hqC.not_nil
    have h1 : 1 < qC.support.length := by
      have hlen := hqC.three_le_length
      rw [qC.length_support]
      omega
    have hsndOpt : qC.support[1]? = some qC.snd := by
      rw [List.getElem?_eq_getElem h1, ← hsnd]
    have hsupportOpt := congrArg (fun l => l[1]?) hqCSupport
    have htarget : qC.support[1]? = some N := by
      simpa [N] using hsupportOpt
    exact Option.some_inj.mp (hsndOpt.symm.trans htarget)
  have hcSnd' : c.snd = N := by
    simpa [closed, d, N, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate,
      setClosed_self] using hcSnd
  have hcEq : c = qC := isCycle_eq_of_isCycles_of_snd_eq
    (fkIsingSquareWiredCompletedLoopGraph_isCycles n hn closed)
    c qC hc hqC (hcSnd'.trans hqCSnd.symm)
  have hrrev : r.reverse.support = N :: r.reverse.support.tail := by
    simpa [N] using r.reverse.cons_tail_support.symm
  have htotal :
      fkIsingSquareWiredTransitionTurn n hn closed E N +
        carrierAdjacentSum
          (fkIsingSquareWiredTransitionTurn n hn closed) r.reverse.support ≡
        8 [ZMOD 16] := by
    rw [hcEq] at hcMod
    have hsumEq : carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn closed) qC.support =
        fkIsingSquareWiredTransitionTurn n hn closed E N +
          carrierAdjacentSum
            (fkIsingSquareWiredTransitionTurn n hn closed)
            r.reverse.support := by
      rw [hqCSupport, hrrev, carrierAdjacentSum_cons_cons]
    have hsumMod :
        fkIsingSquareWiredTransitionTurn n hn closed E N +
            carrierAdjacentSum
              (fkIsingSquareWiredTransitionTurn n hn closed)
              r.reverse.support ≡
          carrierAdjacentSum
            (fkIsingSquareWiredTransitionTurn n hn closed) qC.support
          [ZMOD 16] := by
      rw [hsumEq]
    exact hsumMod.trans hcMod
  let rH := r.mapLe (SimpleGraph.deleteEdges_le _)
  have hreverse :=
    fkIsingSquareWired_carrierAdjacentSum_add_reverse_mod_sixteen
      n hn closed rH
  have hEN : (fkIsingSquareWiredLoopGraph n hn closed).Adj E N := by
    exact Or.inr (by simp [closed, E, N,
      fkIsingSquareWiredTransitionMate,
      FKIsingMedialDart.localMate, setClosed_self])
  have hlocal := fkIsingSquareWiredTransitionTurn_add_reverse_mod_sixteen
    n hn closed hEN
  have hsum :
      (carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed) r.support +
          fkIsingSquareWiredTransitionTurn n hn closed N E) +
        (fkIsingSquareWiredTransitionTurn n hn closed E N +
          carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed)
            r.reverse.support) ≡ 0 [ZMOD 16] := by
    have := hreverse.add hlocal
    simp only [rH, SimpleGraph.Walk.support_mapLe_eq_support,
      SimpleGraph.Walk.support_reverse] at this
    rw [← SimpleGraph.Walk.support_reverse r] at this
    convert this using 1 <;> ring
  have hclosed :
      carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed) r.support +
          fkIsingSquareWiredTransitionTurn n hn closed N E ≡ 8 [ZMOD 16] := by
    have hneg := hsum.sub htotal
    have hminus : (-8 : Int) ≡ 8 [ZMOD 16] := by decide
    convert hneg.trans hminus using 1 <;> ring
  rw [fkIsingSquareWired_carrierAdjacentSum_open_eq_closed_of_deleted_local
    n hn omega e r]
  simpa [closed, N, E] using hclosed

set_option maxHeartbeats 1000000 in

theorem fkIsingSquareWired_one_visit_east_cycle_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (r : ((fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).deleteEdges
        {s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)),
          s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west))}).Walk
            (.dart (e, .west)) (.dart (e, .south)))
    (hr : r.IsPath) :
    carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support +
      fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
        (.dart (e, .south)) (.dart (e, .west)) ≡ 8 [ZMOD 16] := by
  let closed := setClosed e.1 omega
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .west)
  have hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn closed).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source := by
    intro hreach
    apply hwest
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    simpa only [closed, d, fkIsingSquareWiredBlackOfDart] using hreach.symm
  obtain ⟨c, hc, hcSnd, hcTurn⟩ :=
    fkIsingSquareWiredCompletedGraph_exists_carrier_cycle_of_local_black_orbit
      n hn closed d hroot
  have hcMod := fkIsingSquareWired_local_black_orbit_transition_turn_mod_sixteen
    n hn closed d hroot
  dsimp only at hcMod
  rw [← hcTurn] at hcMod
  obtain ⟨q, hq, hqSupport⟩ :=
    fkIsingSquareWired_one_visit_east_carrierCycle
      n hn omega e r hr
  let qC := q.mapLe (show fkIsingSquareWiredLoopGraph n hn closed ≤
      fkIsingSquareWiredCompletedLoopGraph n hn closed from le_sup_left)
  have hqC : qC.IsCycle := hq.mapLe _
  have hqCSupport : qC.support = W :: r.reverse.support := by
    calc
      qC.support = q.support := by
        exact SimpleGraph.Walk.support_mapLe_eq_support _ q
      _ = W :: r.reverse.support := by simpa [W] using hqSupport
  have hqCSnd : qC.snd = S := by
    have hsnd := qC.snd_eq_support_getElem_one hqC.not_nil
    have h1 : 1 < qC.support.length := by
      have hlen := hqC.three_le_length
      rw [qC.length_support]
      omega
    have hsndOpt : qC.support[1]? = some qC.snd := by
      rw [List.getElem?_eq_getElem h1, ← hsnd]
    have hsupportOpt := congrArg (fun l => l[1]?) hqCSupport
    have htarget : qC.support[1]? = some S := by
      simpa [S] using hsupportOpt
    exact Option.some_inj.mp (hsndOpt.symm.trans htarget)
  have hcSnd' : c.snd = S := by
    simpa [closed, d, S, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate,
      setClosed_self] using hcSnd
  have hcEq : c = qC := isCycle_eq_of_isCycles_of_snd_eq
    (fkIsingSquareWiredCompletedLoopGraph_isCycles n hn closed)
    c qC hc hqC (hcSnd'.trans hqCSnd.symm)
  have hrrev : r.reverse.support = S :: r.reverse.support.tail := by
    simpa [S] using r.reverse.cons_tail_support.symm
  have htotal :
      fkIsingSquareWiredTransitionTurn n hn closed W S +
        carrierAdjacentSum
          (fkIsingSquareWiredTransitionTurn n hn closed) r.reverse.support ≡
        8 [ZMOD 16] := by
    rw [hcEq] at hcMod
    have hsumEq : carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn closed) qC.support =
        fkIsingSquareWiredTransitionTurn n hn closed W S +
          carrierAdjacentSum
            (fkIsingSquareWiredTransitionTurn n hn closed)
            r.reverse.support := by
      rw [hqCSupport, hrrev, carrierAdjacentSum_cons_cons]
    have hsumMod :
        fkIsingSquareWiredTransitionTurn n hn closed W S +
            carrierAdjacentSum
              (fkIsingSquareWiredTransitionTurn n hn closed)
              r.reverse.support ≡
          carrierAdjacentSum
            (fkIsingSquareWiredTransitionTurn n hn closed) qC.support
          [ZMOD 16] := by
      rw [hsumEq]
    exact hsumMod.trans hcMod
  let rH := r.mapLe (SimpleGraph.deleteEdges_le _)
  have hreverse :=
    fkIsingSquareWired_carrierAdjacentSum_add_reverse_mod_sixteen
      n hn closed rH
  have hWS : (fkIsingSquareWiredLoopGraph n hn closed).Adj W S := by
    exact Or.inr (by simp [closed, W, S,
      fkIsingSquareWiredTransitionMate,
      FKIsingMedialDart.localMate, setClosed_self])
  have hlocal := fkIsingSquareWiredTransitionTurn_add_reverse_mod_sixteen
    n hn closed hWS
  have hsum :
      (carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed) r.support +
          fkIsingSquareWiredTransitionTurn n hn closed S W) +
        (fkIsingSquareWiredTransitionTurn n hn closed W S +
          carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed)
            r.reverse.support) ≡ 0 [ZMOD 16] := by
    have := hreverse.add hlocal
    simp only [rH, SimpleGraph.Walk.support_mapLe_eq_support,
      SimpleGraph.Walk.support_reverse] at this
    rw [← SimpleGraph.Walk.support_reverse r] at this
    convert this using 1 <;> ring
  have hclosed :
      carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed) r.support +
          fkIsingSquareWiredTransitionTurn n hn closed S W ≡ 8 [ZMOD 16] := by
    have hneg := hsum.sub htotal
    have hminus : (-8 : Int) ≡ 8 [ZMOD 16] := by decide
    convert hneg.trans hminus using 1 <;> ring
  have hopenClosed :=
    fkIsingSquareWired_carrierAdjacentSum_open_eq_closed_of_deleted_local_comm
      n hn omega e r
  rw [hopenClosed]
  simpa [closed, S, W] using hclosed


theorem fkIsingSquareWired_one_visit_west_inserted_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setOpen e.1 omega) (.dart (e, .south)) =
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setClosed e.1 omega) (.dart (e, .south)) := by
  apply fkIsingSquareWired_one_visit_west_inserted_phase_of_cycle_turn_mod_sixteen
    n hn omega e hwest heast
  intro r hr _
  exact fkIsingSquareWired_one_visit_west_cycle_turn_mod_sixteen
    n hn omega e hwest heast r hr


theorem fkIsingSquareWired_one_visit_east_inserted_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setOpen e.1 omega) (.dart (e, .north)) =
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setClosed e.1 omega) (.dart (e, .north)) := by
  apply fkIsingSquareWired_one_visit_east_inserted_phase_of_cycle_turn_mod_sixteen
    n hn omega e hwest heast
  intro r hr _
  exact fkIsingSquareWired_one_visit_east_cycle_turn_mod_sixteen
    n hn omega e hwest heast r hr


theorem fkIsingSquareWired_one_visit_west_exists_closed_macro_walk
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn
        (setClosed e.1 omega)).Walk
        (.inl (fkIsingSquareWiredDartSlot n (e, .east)))
        (.inl (fkIsingSquareWiredDartSlot n (e, .east))),
      ¬p.Nil := by
  let closed := setClosed e.1 omega
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .east)
  have hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn closed).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source := by
    intro hreach
    apply heast
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    simpa only [closed, d, fkIsingSquareWiredBlackOfDart] using hreach.symm
  have havoid :=
    fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source
      n hn closed d hroot
  have hstep := fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
    n hn closed d (havoid 0).1 (havoid 0).2
  have hmove : fkIsingSquareWiredBlackBoundaryPerm n hn closed
      (fkIsingSquareWiredBlackOfDart n d) ≠
        fkIsingSquareWiredBlackOfDart n d := by
    intro heq
    rw [heq] at hstep
    exact fkIsingSquareWiredPortNext_ne n hn closed d
      (fkIsingSquareWiredBlackOfDart_injective n hstep.symm)
  apply fkIsingSquareWiredExpandedGraph_exists_closed_macro_walk
    n hn closed d hmove
  · intro i _
    exact (havoid i).1
  · intro i _
    exact (havoid i).2


theorem fkIsingSquareWired_one_visit_east_exists_closed_macro_walk
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn
        (setClosed e.1 omega)).Walk
        (.inl (fkIsingSquareWiredDartSlot n (e, .west)))
        (.inl (fkIsingSquareWiredDartSlot n (e, .west))),
      ¬p.Nil := by
  let closed := setClosed e.1 omega
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .west)
  have hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn closed).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source := by
    intro hreach
    apply hwest
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    simpa only [closed, d, fkIsingSquareWiredBlackOfDart] using hreach.symm
  have havoid :=
    fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source
      n hn closed d hroot
  have hstep := fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
    n hn closed d (havoid 0).1 (havoid 0).2
  have hmove : fkIsingSquareWiredBlackBoundaryPerm n hn closed
      (fkIsingSquareWiredBlackOfDart n d) ≠
        fkIsingSquareWiredBlackOfDart n d := by
    intro heq
    rw [heq] at hstep
    exact fkIsingSquareWiredPortNext_ne n hn closed d
      (fkIsingSquareWiredBlackOfDart_injective n hstep.symm)
  apply fkIsingSquareWiredExpandedGraph_exists_closed_macro_walk
    n hn closed d hmove
  · intro i _
    exact (havoid i).1
  · intro i _
    exact (havoid i).2


theorem fkIsingSquareWired_one_visit_west_exists_expanded_cycle
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    ∃ root p,
      p.IsCycle ∧
      s((.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n (e, .north))) ∈
        (p : (fkIsingSquareWiredExpandedGraph n hn
          (setClosed e.1 omega)).Walk root root).edges := by
  let closed := setClosed e.1 omega
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .east)
  have hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn closed).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source := by
    intro hreach
    apply heast
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    simpa only [closed, d, fkIsingSquareWiredBlackOfDart] using hreach.symm
  simpa [closed, d, FKIsingMedialDart.localMate, setClosed_self] using
    (fkIsingSquareWiredExpandedGraph_exists_cycle_of_local_black_orbit
      n hn closed d (Or.inr rfl)
        (by simp [closed, d, FKIsingMedialDart.localMate, setClosed_self])
        (by simp [closed, d, FKIsingMedialDart.localMate, setClosed_self]) hroot)


theorem fkIsingSquareWired_one_visit_east_exists_expanded_cycle
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    ∃ root p,
      p.IsCycle ∧
      s((.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n (e, .south))) ∈
        (p : (fkIsingSquareWiredExpandedGraph n hn
          (setClosed e.1 omega)).Walk root root).edges := by
  let closed := setClosed e.1 omega
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .west)
  have hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn closed).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source := by
    intro hreach
    apply hwest
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    simpa only [closed, d, fkIsingSquareWiredBlackOfDart] using hreach.symm
  simpa [closed, d, FKIsingMedialDart.localMate, setClosed_self] using
    (fkIsingSquareWiredExpandedGraph_exists_cycle_of_local_black_orbit
      n hn closed d (Or.inl rfl)
        (by simp [closed, d, FKIsingMedialDart.localMate, setClosed_self])
        (by simp [closed, d, FKIsingMedialDart.localMate, setClosed_self]) hroot)

end
end StatMech.Universality
