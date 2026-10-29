/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecayFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Def.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull
open MeasureTheory Set
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice StatMech.ConfigSpace


variable {d : ℕ}


@[simp]
theorem mem_crossingEventFrom {y : Site d} {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ crossingEventFrom d y n ↔ ∃ v, Connected d ω y v ∧ v ∉ box d (n - 1) :=
  Iff.rfl


theorem crossingEventFrom_origin (n : ℕ) :
    crossingEventFrom d (origin d) n = crossingEvent d n := rfl


theorem measurableSet_crossingEventFrom (y : Site d) (n : ℕ) :
    MeasurableSet (crossingEventFrom d y n) := by
  have hrw : crossingEventFrom d y n
      = ⋃ v ∈ (box d (n - 1))ᶜ,
          {ω : ConfigSpace (Sym2 (Site d)) | Connected d ω y v} := by
    ext ω
    simp only [mem_crossingEventFrom, Set.mem_iUnion, Set.mem_compl_iff, Set.mem_setOf_eq]
    exact ⟨fun ⟨v, hc, hv⟩ => ⟨v, hv, hc⟩, fun ⟨v, hv, hc⟩ => ⟨v, hc, hv⟩⟩
  rw [hrw]
  exact MeasurableSet.biUnion (Set.to_countable _)
    (fun v _ => measurableSet_connected y v)


theorem measurableSet_crossingEvent (n : ℕ) : MeasurableSet (crossingEvent d n) :=
  measurableSet_crossingEventFrom (origin d) n


theorem crossingEventFrom_eq_preimage (y : Site d) (n : ℕ) :
    crossingEventFrom d y n
      = (shift (Multiplicative.ofAdd (-y)) : ConfigSpace (Sym2 (Site d)) → _) ⁻¹'
          {ω | ∃ v, Connected d ω (origin d) v ∧ (v + y) ∉ box d (n - 1)} := by
  ext ω
  simp only [mem_crossingEventFrom, Set.mem_setOf_eq, Set.mem_preimage]
  set g := Multiplicative.ofAdd (-y) with hg
  have hgy : g • y = origin d := by funext i; show -y i + y i = (0 : ℤ); ring
  constructor
  · rintro ⟨v, hc, hv⟩
    refine ⟨g • v, ?_, ?_⟩
    · have hkey := (connected_shift g ω y v).mpr hc
      rwa [hgy] at hkey
    · have hvy : g • v + y = v := by funext i; show (-y i + v i) + y i = v i; ring
      rwa [hvy]
  · rintro ⟨w, hc, hw⟩
    refine ⟨g⁻¹ • w, ?_, ?_⟩
    · have hkey := (connected_shift g ω y (g⁻¹ • w)).mp ?_
      · exact hkey
      · rw [hgy, smul_inv_smul]; exact hc
    · have hgi : g⁻¹ • w = w + y := by
        funext i
        rw [smul_site_apply]
        simp only [hg, ← ofAdd_neg, toAdd_ofAdd, neg_neg, Pi.add_apply]
        ring
      rwa [hgi]


theorem box_shift_mem {y v : Site d} {L m n : ℕ}
    (hy : y ∈ box d L) (hv : v ∈ box d (m - 1)) (hmLn : m + L ≤ n) (hm : 1 ≤ m) :
    (v + y) ∈ box d (n - 1) := by
  intro i
  have hvi : (v i).natAbs ≤ m - 1 := hv i
  have hyi : (y i).natAbs ≤ L := hy i
  have hle : ((v + y) i).natAbs ≤ (v i).natAbs + (y i).natAbs := by
    rw [Pi.add_apply]; exact Int.natAbs_add_le _ _
  omega


theorem crossProbFrom_le (p : NNReal) (hp : p ≤ 1) (y : Site d) {L m n : ℕ}
    (hy : y ∈ box d L) (hmLn : m + L ≤ n) (hm : 1 ≤ m) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (crossingEventFrom d y n)
      ≤ crossProb d p hp m := by
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp with hμ
  set g := Multiplicative.ofAdd (-y) with hg
  set B := {ω : ConfigSpace (Sym2 (Site d)) |
      ∃ v, Connected d ω (origin d) v ∧ (v + y) ∉ box d (n - 1)} with hB
  
  have hBmeas : MeasurableSet B := by
    have hrw : B = ⋃ v ∈ {v : Site d | (v + y) ∉ box d (n - 1)},
        {ω : ConfigSpace (Sym2 (Site d)) | Connected d ω (origin d) v} := by
      ext ω; simp only [hB, Set.mem_setOf_eq, Set.mem_iUnion]
      exact ⟨fun ⟨v, hc, hv⟩ => ⟨v, hv, hc⟩, fun ⟨v, hv, hc⟩ => ⟨v, hc, hv⟩⟩
    rw [hrw]
    exact MeasurableSet.biUnion (Set.to_countable _)
      (fun v _ => measurableSet_connected (origin d) v)
  
  have hpres := (bernoulli_translationInvariant (E := Sym2 (Site d))
    (G := Multiplicative (Site d)) p hp) g
  have hstep1 : μ.real (crossingEventFrom d y n) = μ.real B := by
    rw [crossingEventFrom_eq_preimage]
    exact hpres.measureReal_preimage hBmeas.nullMeasurableSet
  rw [hstep1]
  
  have hsub : B ⊆ crossingEvent d m := by
    rintro ω ⟨v, hc, hv⟩
    exact ⟨v, hc, fun hvm => hv (box_shift_mem hy hvm hmLn hm)⟩
  calc μ.real B ≤ μ.real (crossingEvent d m) := measureReal_mono hsub
    _ = crossProb d p hp m := rfl


theorem subcritical_decay_full (p : NNReal) (hp : p ≤ 1) (S : Finset (Site d))
    (hS0 : origin d ∈ S) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L)
    (hstep : ∀ k, crossProb d p hp ((k + 1) * L)
      ≤ phi d p hp S * crossProb d p hp (k * L)) :
    ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n) :=
  subcritical_decay p hp S hS0 hphi L hL hstep

end Percolation
end StatMech
