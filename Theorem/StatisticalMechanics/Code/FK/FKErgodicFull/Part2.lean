/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Def.StatisticalMechanics.Code.FK.FKErgodicFull
open MeasureTheory Filter Topology
open StatMech.ConfigSpace StatMech.Lattice


namespace StatMech

namespace FK

variable {d : ℕ}


theorem erg_wiredIV_map_shift {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d))
    (hshift : ∀ φ : ℕ → ℕ, StrictMono φ →
        WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
          (wiredInfiniteVolume d hp hp1 hq) →
        WeakConvergesTo (fun n => erg_wiredShiftedFinite hp hp1 hq g (φ n))
          (wiredInfiniteVolume d hp hp1 hq)) :
    Measure.map (shift g)
        (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))
      = (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
  obtain ⟨φ, hφ, hconv⟩ := wiredInfiniteVolume_isLimit d hp hp1 hq
  exact erg_measure_map_eq_of_translated_converges
    (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq) (wiredInfiniteVolume d hp hp1 hq)
    (continuous_shift g) hconv (hshift φ hφ hconv)


theorem erg_freeIV_map_shift {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d))
    (hshift : ∀ φ : ℕ → ℕ, StrictMono φ →
        WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
          (freeInfiniteVolume d hp hp1 hq) →
        WeakConvergesTo (fun n => erg_freeShiftedFinite hp hp1 hq g (φ n))
          (freeInfiniteVolume d hp hp1 hq)) :
    Measure.map (shift g)
        (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))
      = (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
  obtain ⟨φ, hφ, hconv⟩ := freeInfiniteVolume_isLimit d hp hp1 hq
  exact erg_measure_map_eq_of_translated_converges
    (fun n => freeFiniteMeasure d (φ n) hp hp1 hq) (freeInfiniteVolume d hp hp1 hq)
    (continuous_shift g) hconv (hshift φ hφ hconv)


theorem erg_wiredIV_isTranslationInvariant {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hshift : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
          (wiredInfiniteVolume d hp hp1 hq) →
        WeakConvergesTo (fun n => erg_wiredShiftedFinite hp hp1 hq g (φ n))
          (wiredInfiniteVolume d hp hp1 hq)) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro g
  exact ⟨measurable_shift g, erg_wiredIV_map_shift hp hp1 hq g (hshift g)⟩


theorem erg_freeIV_isTranslationInvariant {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hshift : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
          (freeInfiniteVolume d hp hp1 hq) →
        WeakConvergesTo (fun n => erg_freeShiftedFinite hp hp1 hq g (φ n))
          (freeInfiniteVolume d hp hp1 hq)) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro g
  exact ⟨measurable_shift g, erg_freeIV_map_shift hp hp1 hq g (hshift g)⟩

end FK
end StatMech
