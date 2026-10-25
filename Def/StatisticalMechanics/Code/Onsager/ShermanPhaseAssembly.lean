/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLemma5
import Theorem.StatisticalMechanics.Code.Onsager.KWSpectral.Part2


namespace StatMech.Onsager

open Matrix BigOperators

noncomputable def ons_phaseBucketE
    (L : ℕ) [NeZero L] (x omega : ℂ) (a b : Fin 2)
    (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
      (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)),
    ons_loopWeight (ons_KWmatPhase L x omega
      (ons_spinPhase L a) (ons_spinPhase L b)) d

noncomputable def ons_phaseBucketN
    (L : ℕ) [NeZero L] (x omega : ℂ) (a b : Fin 2)
    (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
      ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)),
    ons_loopWeight (ons_KWmatPhase L x omega
      (ons_spinPhase L a) (ons_spinPhase L b)) d

noncomputable def ons_maskPhaseBucketE
    (L : ℕ) [NeZero L] (x omega : ℂ) (a b : Fin 2)
    (forbidden : Finset (ons_Dart L)) (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
      (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)),
    ons_loopWeight
      (ons_maskMatrix forbidden (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))) d

noncomputable def ons_maskPhaseBucketN
    (L : ℕ) [NeZero L] (x omega : ℂ) (a b : Fin 2)
    (forbidden : Finset (ons_Dart L)) (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
      ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)),
    ons_loopWeight
      (ons_maskMatrix forbidden (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))) d

end StatMech.Onsager
