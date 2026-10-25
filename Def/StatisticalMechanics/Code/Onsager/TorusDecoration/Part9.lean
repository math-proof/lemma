/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.TrivalentCycles
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part8


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

def ons_portBit {L : ℕ} (F : Finset (Sym2 (ZMod L × ZMod L)))
    (d : ons_Dart L) : Fin 2 :=
  if ons_portEdge L d ∈ F then 1 else 0

noncomputable def ons_evenSubgraphPortPattern (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L)) : ons_PortPattern L where
  bit := ons_portBit F
  rev_bit := by
    intro d
    simp only [ons_portBit, ons_portEdge_rev]
  site_even := by
    intro v
    have hdata := hF
    rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
    have hFeq : F = (onsTorusGraph L).edgeFinset.filter (fun e => e ∈ F) := by
      ext e
      simp only [Finset.mem_filter]
      constructor
      · intro he
        exact ⟨hdata.1 he, he⟩
      · exact And.right
    have hcast : ((incCount F v : ℕ) : ZMod 2) = 0 := by
      apply (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mpr
      exact even_iff_two_dvd.mp (hdata.2 v)
    have hsum := ons_cast_incCount_filter_eq_neighbor_sum
      (onsTorusGraph L) (fun e => e ∈ F) v
    rw [← hFeq, hcast] at hsum
    rw [ons_torus_neighbor_sum_eq_direction_sum] at hsum
    simp only [ons_portBit]
    simpa only [ons_portEdge, Fin.sum_univ_four, add_assoc] using hsum.symm

def ons_decoratedPortBit {L : ℕ}
    (D : Finset (Sym2 (ons_Dart L))) (d : ons_Dart L) : Fin 2 :=
  if s(d, ons_dartRev L d) ∈ D then 1 else 0

def ons_decoratedChainBits {L : ℕ}
    (D : Finset (Sym2 (ons_Dart L))) (s : ZMod L × ZMod L) :
    Fin 3 → Fin 2 :=
  ![if s((s, 0), (s, 1)) ∈ D then 1 else 0,
    if s((s, 1), (s, 2)) ∈ D then 1 else 0,
    if s((s, 2), (s, 3)) ∈ D then 1 else 0]

end StatMech.Onsager
