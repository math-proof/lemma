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
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAspectComparison.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicPlanarDualPair.CrossNestedOutwardPowerAspectComparison.nonempty_endpointCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (comparison : D.CrossNestedOutwardPowerAspectComparison mu)
    (preparation : D.CrossNestedOutwardArrayPreparation mu)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu)) :
    Nonempty (D.CrossNestedOutwardEndpointCertificate mu) := by
  let epsilon : Nat -> Real := fun n =>
    1 / ((n + 1 : Real) * (comparison.exponent n + 1 : Nat))
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  have hepsilon_le (n : Nat) : epsilon n <= 1 / (n + 1 : Real) := by
    dsimp only [epsilon]
    have hn : 0 < (n + 1 : Real) := by positivity
    have hm : 1 <= ((comparison.exponent n + 1 : Nat) : Real) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (comparison.exponent n))
    apply one_div_le_one_div_of_le hn
    nlinarith
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    apply squeeze_zero (fun n => (hepsilon n).le) hepsilon_le
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  obtain ⟨rebuilt, hverticalLower, hvertical⟩ :=
    preparation.exists_verticalEndpoint_rebuild_at_error D mu
      hFKG hTI hunique hTIDual epsilon hepsilon hepsilonZero
  let vertical : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      ((rebuilt.array.chain n).level 0).raw.data.wideLeft
      ((rebuilt.array.chain n).level 0).raw.data.wideRight 0
      ((rebuilt.array.chain n).extentY 0))
  let horizontal : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent 0
      ((rebuilt.array.chain n).extentX (2 * (n + 1) + 2)) 0
      ((rebuilt.array.chain n).extentY (2 * (n + 1) + 2)))
  have hweightedError (n : Nat) :
      (comparison.exponent n : Real) * epsilon n <=
        1 / (n + 1 : Real) := by
    dsimp only [epsilon]
    have hn : 0 < (n + 1 : Real) := by positivity
    have hm : 0 < ((comparison.exponent n + 1 : Nat) : Real) := by
      positivity
    have hfactor : (comparison.exponent n : Real) /
        (comparison.exponent n + 1 : Nat) <= 1 := by
      apply (div_le_one hm).2
      push_cast
      linarith
    calc
      (comparison.exponent n : Real) *
          (1 / ((n + 1 : Real) *
            (comparison.exponent n + 1 : Nat))) =
        ((comparison.exponent n : Real) /
            (comparison.exponent n + 1 : Nat)) *
            (1 / (n + 1 : Real)) := by
              field_simp
      _ <= 1 * (1 / (n + 1 : Real)) :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = 1 / (n + 1 : Real) := one_mul _
  have hweightedErrorZero : Tendsto
      (fun n => (comparison.exponent n : Real) * epsilon n)
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact mul_nonneg (Nat.cast_nonneg _) (hepsilon n).le
    · exact hweightedError
    · simpa using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hlower : Tendsto (fun n =>
      1 - (comparison.exponent n : Real) * epsilon n)
      atTop (nhds 1) := by
    simpa using
      (tendsto_const_nhds (x := (1 : Real))).sub hweightedErrorZero
  have hhorizontal : Tendsto horizontal atTop (nhds 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower tendsto_const_nhds
    · intro n
      have hv0 : 0 <= vertical n := measureReal_nonneg
      have hv1 : vertical n <= 1 := measureReal_le_one
      have heps1 : epsilon n <= 1 :=
        (hepsilon_le n).trans (by
          have hn : (1 : Real) <= n + 1 := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          simpa using one_div_le_one_div_of_le (by norm_num) hn)
      have hbase0 : 0 <= 1 - epsilon n := sub_nonneg.mpr heps1
      have hbaseV : 1 - epsilon n <= vertical n :=
        le_of_lt (by simpa only [vertical] using hverticalLower n)
      calc
        1 - (comparison.exponent n : Real) * epsilon n =
            1 - (comparison.exponent n : Real) *
              (1 - (1 - epsilon n)) := by ring
        _ <= (1 - epsilon n) ^ comparison.exponent n :=
          one_sub_nat_mul_one_sub_le_pow (1 - epsilon n)
            (comparison.exponent n) hbase0 (by linarith)
        _ <= (vertical n) ^ comparison.exponent n := by
          exact pow_le_pow_left₀ hbase0 hbaseV _
        _ <= horizontal n := by
          simpa only [vertical, horizontal] using
            comparison.horizontalEnd_ge_verticalStart_pow rebuilt n
    · intro n
      exact measureReal_le_one
  exact ⟨{
    preparation := rebuilt
    verticalStart := by simpa only [vertical] using hvertical
    horizontalEnd := by simpa only [horizontal] using hhorizontal }⟩


theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_powerAspectComparison
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hcomparison :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        D.CrossNestedOutwardPowerAspectComparison mu) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only
  intro hcommon
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  have hmodel := D.freeBufferedInfiniteVolume_sheffieldData_of_common
    hp hp1 hq hcommon
  obtain ⟨preparation⟩ :=
    D.exists_canonicalCrossNestedOutwardArrayPreparation_of_common
      hp hp1 hq hcommon
  have comparison : D.CrossNestedOutwardPowerAspectComparison mu :=
    hcomparison hcommon
  obtain ⟨certificate⟩ := comparison.nonempty_endpointCertificate
    D mu preparation hmodel.1 hmodel.2.1 hmodel.2.2.2.2.1
      hmodel.2.2.2.1
  exact certificate.false D mu hmodel.1 hmodel.2.1
    hmodel.2.2.2.2.1 hmodel.2.2.2.1


theorem PeriodicPlanarDualPair.strictDualNoCoexistence_of_powerAspectComparison_logisticCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 <= q)
    (hcomparison : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        D.CrossNestedOutwardPowerAspectComparison mu)
    (hagrees :
      P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    StrictDualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q := by
  apply D.strictDualNoCoexistence_of_sheffieldNotFull_logisticCylinders
    hconn hconnDual hq
  · intro p hp hp1
    exact D.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_powerAspectComparison
      hp hp1 hq (hcomparison p hp hp1)
  · exact hagrees


theorem PeriodicPlanarDualPair.dualCritical_relation_of_bidirectionalDecay_powerAspectComparison_logisticCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D)
    (Hdual : PolynomialConnectionShells D.swap)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 <= q)
    (hdecay : SubcriticalTwoPointExponentialDecay
      P q (P.criticalPoint q))
    (hdecayDual : SubcriticalTwoPointExponentialDecay
      Pdual q (Pdual.criticalPoint q))
    (hcomparison : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        D.CrossNestedOutwardPowerAspectComparison mu)
    (hagrees :
      P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  apply D.dualCritical_relation_of_bidirectionalExponentialDecay_strictNoCoexistence
    H Hdual hq hdecay hdecayDual
  exact D.strictDualNoCoexistence_of_powerAspectComparison_logisticCylinders
    hconn hconnDual hq hcomparison hagrees


theorem PeriodicPlanarDualPair.dualCritical_relation_of_bidirectionalDecay_aspectGluing_logisticCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D)
    (Hdual : PolynomialConnectionShells D.swap)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 <= q)
    (hdecay : SubcriticalTwoPointExponentialDecay
      P q (P.criticalPoint q))
    (hdecayDual : SubcriticalTwoPointExponentialDecay
      Pdual q (Pdual.criticalPoint q))
    (hgluing : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        D.CrossNestedOutwardAspectGluing mu)
    (hagrees :
      P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  apply D.dualCritical_relation_of_bidirectionalDecay_powerAspectComparison_logisticCylinders
    H Hdual hconn hconnDual hq hdecay hdecayDual
  · intro p hp hp1
    dsimp only
    intro hcommon
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    have hmodel := D.freeBufferedInfiniteVolume_sheffieldData_of_common
      hp hp1 hq hcommon
    exact (hgluing p hp hp1 hcommon).toPowerComparison D mu hmodel.1
  · exact hagrees

end StatMech.FK.PeriodicPlanar
