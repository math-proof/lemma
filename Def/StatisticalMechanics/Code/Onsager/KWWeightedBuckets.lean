/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedBuckets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.KWWeightedCancellation
import Theorem.StatisticalMechanics.Code.Onsager.ShermanPhaseAssembly.Part5


namespace StatMech.Onsager

open Matrix BigOperators

noncomputable def ons_weightedPhaseBucketE
    (L : ℕ) [NeZero L]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (a b : Fin 2)
    (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
      (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)),
    ons_loopWeight (ons_KWmatWeightedPhase L weight omega
      (ons_spinPhase L a) (ons_spinPhase L b)) d

noncomputable def ons_weightedPhaseBucketN
    (L : ℕ) [NeZero L]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (a b : Fin 2)
    (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
      ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)),
    ons_loopWeight (ons_KWmatWeightedPhase L weight omega
      (ons_spinPhase L a) (ons_spinPhase L b)) d

noncomputable def ons_maskWeightedPhaseBucketE
    (L : ℕ) [NeZero L]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (a b : Fin 2)
    (forbidden : Finset (ons_Dart L)) (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
      (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)),
    ons_loopWeight
      (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega
        (ons_spinPhase L a) (ons_spinPhase L b))) d

noncomputable def ons_maskWeightedPhaseBucketN
    (L : ℕ) [NeZero L]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (a b : Fin 2)
    (forbidden : Finset (ons_Dart L)) (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
      ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)),
    ons_loopWeight
      (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega
        (ons_spinPhase L a) (ons_spinPhase L b))) d

end StatMech.Onsager
