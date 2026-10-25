/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part8
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


section Countable

variable [Countable V]


theorem PeriodicGraph.wiredInfiniteVolume_isLimit (P : PeriodicGraph V)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      WeakConvergesTo (fun n => P.wiredFiniteMeasure (phi n) hp hp1 hq)
        (P.wiredInfiniteVolume hp hp1 hq) := by
  obtain ⟨phi, hphi, hlimit⟩ :=
    (prokhorov_seq_compact (fun n => P.wiredFiniteMeasure n hp hp1 hq)).choose_spec
  exact ⟨phi, hphi, hlimit⟩

end Countable


theorem siteTranslate_zero : siteTranslate (0 : Site 2) = Equiv.refl (Site 2) := by
  ext x i
  simp

theorem siteTranslate_add (z w v : Site 2) :
    siteTranslate (z + w) v = siteTranslate w (siteTranslate z v) := by
  ext i
  simp [add_assoc]

theorem square_shift_adj (z x y : Site 2) :
    (hypercubicLattice 2).Adj (siteTranslate z x) (siteTranslate z y) ↔
      (hypercubicLattice 2).Adj x y := by
  simp only [hypercubicLattice_adj, siteTranslate_apply]
  have hsums :
      (∑ i, ((x + z) i - (y + z) i).natAbs) =
        ∑ i, (x i - y i).natAbs := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp [Pi.add_apply]
  rw [hsums]


end PeriodicPlanar
end FK
end StatMech
