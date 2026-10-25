/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces.Part3
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ArcNoSeparation.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ArcExteriorClose.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {V : Type*}


theorem tnbp_reroute_avoiding (G G' : SimpleGraph V) (c : V)
    (hG' : ∀ a b, G'.Adj a b ↔ G.Adj a b ∧ a ≠ c ∧ b ≠ c)
    (hneigh : ∀ p q, G.Adj c p → G.Adj c q → G'.Reachable p q) :
    ∀ {x y : V} (_w : G.Walk x y) (a : V), a ≠ c →
      (x = c → G.Adj a c) → (x ≠ c → G'.Reachable a x) →
      y ≠ c → G'.Reachable a y := by
  classical
  intro x y w
  induction w with
  | nil =>
    intro a _ _ hxn hy
    exact hxn hy
  | @cons x z y' h p ih =>
    intro a ha hxc hxn hy'
    by_cases hxc' : x = c
    · 
      have hcz : G.Adj c z := hxc' ▸ h
      by_cases hzc : z = c
      · exact ih a ha (fun _ => hxc hxc') (fun hzn => absurd hzc hzn) hy'
      · 
        have hreach : G'.Reachable a z := hneigh a z (hxc hxc').symm hcz
        exact ih a ha (fun hh => absurd hh hzc) (fun _ => hreach) hy'
    · 
      have hax : G'.Reachable a x := hxn hxc'
      by_cases hzc : z = c
      · 
        have hxcadj : G.Adj x c := hzc ▸ h
        exact hax.trans (ih x hxc' (fun _ => hxcadj) (fun hh => absurd hzc hh) hy')
      · 
        have hxz : G'.Adj x z := (hG' x z).mpr ⟨h, hxc', hzc⟩
        have haz : G'.Reachable a z := hax.trans hxz.reachable
        exact ih a ha (fun hh => absurd hh hzc) (fun _ => haz) hy'


theorem tnbp_reachable_of_avoid (G G' : SimpleGraph V) (c : V)
    (hG' : ∀ a b, G'.Adj a b ↔ G.Adj a b ∧ a ≠ c ∧ b ≠ c)
    (hneigh : ∀ p q, G.Adj c p → G.Adj c q → G'.Reachable p q)
    {x y : V} (hx : x ≠ c) (hy : y ≠ c) (hr : G.Reachable x y) : G'.Reachable x y := by
  obtain ⟨w⟩ := hr
  exact tnbp_reroute_avoiding G G' c hG' hneigh w x hx (fun hh => absurd hh hx)
    (fun _ => Reachable.refl _) hy


theorem tnbp_insert_adj_iff (c : Site 2) (B : Set (Site 2)) (a b : Site 2) :
    (ffc_offSupportLattice (insert c B)).Adj a b ↔
      (ffc_offSupportLattice B).Adj a b ∧ a ≠ c ∧ b ≠ c := by
  simp only [ffc_offSupportLattice_adj, Set.mem_insert_iff, not_or]
  tauto


end Lattice
end StatMech
