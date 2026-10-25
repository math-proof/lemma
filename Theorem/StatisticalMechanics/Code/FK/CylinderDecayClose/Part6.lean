/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IntegralDecayClose.Part5
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Def.StatisticalMechanics.Code.FK.CylinderDecayClose.Part5
open MeasureTheory Filter Topology BoundedContinuousFunction SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


theorem cdc_cylinderAlg_le_wiredDecaySet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hhom : cdc_wiredMultiHomogeneous hp hp1 g) :
    Subalgebra.toSubmodule (idc_cylinderAlg d) ≤ cdc_wiredDecaySet hp hp1 g φ := by
  unfold idc_cylinderAlg
  rw [Algebra.adjoin_eq_span]
  rw [Submodule.span_le]
  intro h hh
  obtain ⟨s, rfl⟩ := cdc_closure_isMonomial hh
  
  show Tendsto (isd_decayFun
      (fun n => wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)) g
      (BoundedContinuousFunction.mkOfCompact (cdc_monomialCM s))) atTop (𝓝 0)
  have := cdc_decayFun_monomial_wired_tendsto_zero hp hp1 g φ hφ hhom s
  exact this


theorem cdc_cylinderAlg_le_freeDecaySet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hhom : cdc_freeMultiHomogeneous hp hp1 g) :
    Subalgebra.toSubmodule (idc_cylinderAlg d) ≤ cdc_freeDecaySet hp hp1 g φ := by
  unfold idc_cylinderAlg
  rw [Algebra.adjoin_eq_span]
  rw [Submodule.span_le]
  intro h hh
  obtain ⟨s, rfl⟩ := cdc_closure_isMonomial hh
  show Tendsto (isd_decayFun
      (fun n => freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)) g
      (BoundedContinuousFunction.mkOfCompact (cdc_monomialCM s))) atTop (𝓝 0)
  exact cdc_decayFun_monomial_free_tendsto_zero hp hp1 g φ hφ hhom s


theorem cdc_wiredCylinderDecay {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hhom : cdc_wiredMultiHomogeneous hp hp1 g) :
    idc_wiredCylinderDecay hp hp1 (by norm_num : (0:ℝ) < 2) g φ := by
  intro f hf
  obtain ⟨h, hhmem, rfl⟩ := hf
  exact cdc_cylinderAlg_le_wiredDecaySet hp hp1 g φ hφ hhom hhmem


theorem cdc_freeCylinderDecay {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hhom : cdc_freeMultiHomogeneous hp hp1 g) :
    idc_freeCylinderDecay hp hp1 (by norm_num : (0:ℝ) < 2) g φ := by
  intro f hf
  obtain ⟨h, hhmem, rfl⟩ := hf
  exact cdc_cylinderAlg_le_freeDecaySet hp hp1 g φ hφ hhom hhmem


theorem cdc_wiredMultiHomogeneous_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    cdc_wiredMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) := by
  intro s
  have hs : s.image (fun e => (1 : Multiplicative (Site d))⁻¹ • e) = s := by
    rw [show (fun e : Sym2 (Site d) => (1 : Multiplicative (Site d))⁻¹ • e)
        = (fun e => e) from by funext e; rw [inv_one, one_smul]]
    exact Finset.image_id
  rw [hs]


theorem cdc_freeMultiHomogeneous_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    cdc_freeMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) := by
  intro s
  have hs : s.image (fun e => (1 : Multiplicative (Site d))⁻¹ • e) = s := by
    rw [show (fun e : Sym2 (Site d) => (1 : Multiplicative (Site d))⁻¹ • e)
        = (fun e => e) from by funext e; rw [inv_one, one_smul]]
    exact Finset.image_id
  rw [hs]


theorem cdc_wiredCylinderDecay_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) :
    idc_wiredCylinderDecay hp hp1 (by norm_num : (0:ℝ) < 2) (1 : Multiplicative (Site d)) φ :=
  cdc_wiredCylinderDecay hp hp1 (1 : Multiplicative (Site d)) φ hφ
    (cdc_wiredMultiHomogeneous_one hp hp1)


theorem cdc_wiredIV_isTranslationInvariant_of_homogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hhom : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2))
          (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)) →
        cdc_wiredMultiHomogeneous hp hp1 g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  idc_wiredIV_isTranslationInvariant_of_cylinderDecay hp hp1 (by norm_num : (0:ℝ) < 2)
    (fun g φ hφ hconv => cdc_wiredCylinderDecay hp hp1 g φ hφ (hhom g φ hφ hconv))


theorem cdc_freeIV_isTranslationInvariant_of_homogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hhom : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2))
          (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)) →
        cdc_freeMultiHomogeneous hp hp1 g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  idc_freeIV_isTranslationInvariant_of_cylinderDecay hp hp1 (by norm_num : (0:ℝ) < 2)
    (fun g φ hφ hconv => cdc_freeCylinderDecay hp hp1 g φ hφ (hhom g φ hφ hconv))

end FK
end StatMech
