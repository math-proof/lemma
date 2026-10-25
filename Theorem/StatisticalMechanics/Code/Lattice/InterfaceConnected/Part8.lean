/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Def.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part7
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem orbitReached_of_kingReachable (K : Set (Site 2)) (htr : OrbitKingTransport K)
    (e : Dart) (he : IsBoundaryDart K e) {u w : Site 2} (hu : u ∉ K) (hw : w ∉ K)
    (hreach : (boundaryKingGraph K).Reachable ⟨u, hu⟩ ⟨w, hw⟩)
    (hou : OrbitReached K e u) : OrbitReached K e w := by
  obtain ⟨p⟩ := hreach
  suffices H : ∀ (a b : ↥(Kᶜ : Set (Site 2))), (boundaryKingGraph K).Walk a b →
      OrbitReached K e (a : Site 2) → OrbitReached K e (b : Site 2) from
    H ⟨u, hu⟩ ⟨w, hw⟩ p hou
  intro a b q
  induction q with
  | nil => intro h; exact h
  | @cons a b c hadj q' ih =>
    intro hoa
    have hking : KingAdj (a : Site 2) (b : Site 2) := (boundaryKingGraph_adj K a b).mp hadj
    have ho_b : OrbitReached K e (b : Site 2) := htr e he a.2 b.2 hking hoa
    exact ih ho_b


theorem interfaceConnected_of_kingResidues (K : Set (Site 2))
    (htr : OrbitKingTransport K) (hcon : BoundaryKingConnected K)
    (hsat : OrbitVertexSaturate K) :
    InterfaceConnected K := by
  intro e f he hf hreach
  
  have hking : (boundaryKingGraph K).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ :=
    hcon he.2 hf.2 hreach
  
  have hbase : OrbitReached K e e.head := orbitReached_self K e he
  have hfhead : OrbitReached K e f.head :=
    orbitReached_of_kingReachable K htr e he he.2 hf.2 hking hbase
  
  exact hsat e he hfhead f hf rfl

end Lattice
end StatMech
