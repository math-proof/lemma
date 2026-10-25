/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint.Part9
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCrossingGluing.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictCriticalAssembly
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictNoCoexistenceClosure.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicPlaneEmbedding.horizontalCrossing_translate_measureReal_eq
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    (a b c d : Real) :
    mu.real (E.horizontalCrossingEvent
      (a + (z 0 : Real)) (b + (z 0 : Real))
      (c + (z 1 : Real)) (d + (z 1 : Real))) =
      mu.real (E.horizontalCrossingEvent a b c d) := by
  apply le_antisymm
  · have h := E.horizontalCrossing_translate_measureReal_le
      mu hTI (-z) (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))
    simpa using h
  · exact E.horizontalCrossing_translate_measureReal_le
      mu hTI z a b c d


theorem PeriodicPlaneEmbedding.verticalCrossing_translate_measureReal_eq
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    (a b c d : Real) :
    mu.real (E.verticalCrossingEvent
      (a + (z 0 : Real)) (b + (z 0 : Real))
      (c + (z 1 : Real)) (d + (z 1 : Real))) =
      mu.real (E.verticalCrossingEvent a b c d) := by
  apply le_antisymm
  · have h := E.verticalCrossing_translate_measureReal_le
      mu hTI (-z) (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))
    simpa using h
  · exact E.verticalCrossing_translate_measureReal_le
      mu hTI z a b c d


theorem PeriodicPlaneEmbedding.verticalCrossing_measureReal_le_translate_enlarge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    {a b a' b' c d : Real}
    (ha : a' <= a + (z 0 : Real)) (hb : b + (z 0 : Real) <= b') :
    mu.real (E.verticalCrossingEvent a b c d) <=
      mu.real (E.verticalCrossingEvent a' b'
        (c + (z 1 : Real)) (d + (z 1 : Real))) := by
  rw [<- E.verticalCrossing_translate_measureReal_eq mu hTI z a b c d]
  exact measureReal_mono
    (E.verticalCrossingEvent_mono_horizontal ha hb)


theorem PeriodicPlaneEmbedding.horizontalCrossing_measureReal_le_translate_enlarge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    {a b c d c' d' : Real}
    (hc : c' <= c + (z 1 : Real)) (hd : d + (z 1 : Real) <= d') :
    mu.real (E.horizontalCrossingEvent a b c d) <=
      mu.real (E.horizontalCrossingEvent
        (a + (z 0 : Real)) (b + (z 0 : Real)) c' d') := by
  rw [<- E.horizontalCrossing_translate_measureReal_eq mu hTI z a b c d]
  exact measureReal_mono
    (E.horizontalCrossingEvent_mono_vertical hc hd)


theorem one_sub_nat_mul_one_sub_le_pow (x : Real) (n : Nat)
    (hx0 : 0 <= x) (hx1 : x <= 1) :
    1 - (n : Real) * (1 - x) <= x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow0 : 0 <= x ^ n := pow_nonneg hx0 n
      have hpow1 : x ^ n <= 1 := pow_le_one₀ hx0 hx1
      calc
        1 - ((n + 1 : Nat) : Real) * (1 - x) =
            (1 - (n : Real) * (1 - x)) - (1 - x) := by
              push_cast
              ring
        _ <= x ^ n - (1 - x) := sub_le_sub_right ih _
        _ <= x ^ n * x := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hx1)
            (sub_nonneg.mpr hpow1)]
        _ = x ^ (n + 1) := by rw [pow_succ]


end StatMech.FK.PeriodicPlanar
