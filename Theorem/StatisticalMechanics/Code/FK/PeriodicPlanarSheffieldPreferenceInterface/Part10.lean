/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part9
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem preferenceRightFlagChain_of_path {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (hbottom : (preferenceInterfaceGraph color).degree (.bottom) = 0)
    (htop : (preferenceInterfaceGraph color).degree (.top) = 0) :
    ∀ {u z : PreferenceInterfaceNode n m}
      (p : (preferenceInterfaceGraph color).Walk u z),
      z = .right → p.IsPath → .left ∉ p.support →
      ∀ t : PreferenceTriangle n m, u = .triangle t →
        PreferenceRightFlagChain color t := by
  intro u z p
  induction p with
  | nil =>
      intro hz _hp _hleft t hut
      have : False := by simpa using hut.symm.trans hz
      exact this.elim
  | @cons u v w huv q ih =>
      intro hw hp hleft t hut
      subst u
      obtain ⟨k, hk, hv⟩ :=
        (preferenceInterfaceAdj_triangle_iff color t v).1 huv
      have hpq : q.IsPath := (Walk.cons_isPath_iff huv q).1 hp |>.1
      have hleftq : PreferenceInterfaceNode.left ∉ q.support := by
        intro hmem
        exact hleft (by simp [hmem])
      cases hnode : preferenceTriangleOther t k with
      | left =>
          have hvl : v = PreferenceInterfaceNode.left := hv.trans hnode
          have hmem : v ∈ q.support := by simp
          exact (hleftq (hvl ▸ hmem)).elim
      | right =>
          exact PreferenceRightFlagChain.last hk hnode
      | bottom =>
          have hiso := (degree_eq_zero
            (preferenceInterfaceGraph color) (.bottom)).1 hbottom
          exact (hiso _ ((hv.trans hnode) ▸ huv.symm)).elim
      | top =>
          have hiso := (degree_eq_zero
            (preferenceInterfaceGraph color) (.top)).1 htop
          exact (hiso _ ((hv.trans hnode) ▸ huv.symm)).elim
      | triangle s =>
          exact PreferenceRightFlagChain.cons hk hnode
            (ih hw hpq hleftq s (hv.trans hnode))

theorem preferenceFlagCrossing_of_reachable {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (hbottom : (preferenceInterfaceGraph color).degree (.bottom) = 0)
    (htop : (preferenceInterfaceGraph color).degree (.top) = 0)
    (hreach : (preferenceInterfaceGraph color).Reachable (.left) (.right)) :
    PreferenceFlagCrossing color := by
  classical
  obtain ⟨w⟩ := hreach
  rcases w.toPath with ⟨p, hp⟩
  cases p with
  | @cons u v z huv q =>
      have hpath := (Walk.cons_isPath_iff huv q).1 hp
      change preferenceInterfaceAdj color .left v at huv
      obtain ⟨t, k, hk, hother, hv⟩ :=
        (preferenceInterfaceAdj_exterior_iff color .left (by simp) v).1 huv
      refine ⟨t, k, hk, hother, ?_⟩
      exact preferenceRightFlagChain_of_path color hbottom htop q rfl
        hpath.1 hpath.2 t hv

end StatMech.FK.PeriodicPlanar
