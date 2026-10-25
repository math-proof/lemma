/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.FK.TwoPointInfinite.Part5
import Theorem.StatisticalMechanics.Code.FK.BoxTailLimit
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.FreeWiredAgreeClose.Part3
import Theorem.StatisticalMechanics.Code.Ising.TransitionFK
import Def.StatisticalMechanics.Code.Exact3D.FKTwoPointQ2Bridge.Part5
open Filter
open MeasureTheory


namespace StatMech

namespace Exact3D

open FK


theorem fkTwoSidedFreeIVQ2_of_freeFiniteVolumeBoundsOfBeta
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hbounds :
      FreeFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi mass := by
  rcases hbounds with
    ⟨hlo_pos, hhi_pos, hlo_log, hhi_log, hlo, hhi⟩
  simpa [freeInfiniteVolumeXAxisConnectionOfBetaQ2] using
    fkTwoSidedFreeIVQ2_of_eventually_boxConnEvent_bounds
      (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
      hlo_pos hhi_pos hlo_log hhi_log hlo hhi


theorem fkTwoSidedWiredIVQ2_of_wiredFiniteVolumeBoundsOfBeta
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hbounds :
      WiredFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi mass := by
  rcases hbounds with
    ⟨hlo_pos, hhi_pos, hlo_log, hhi_log, hlo, hhi⟩
  simpa [wiredInfiniteVolumeXAxisConnectionOfBetaQ2] using
    fkTwoSidedWiredIVQ2_of_eventually_boxConnEvent_bounds
      (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
      hlo_pos hhi_pos hlo_log hhi_log hlo hhi


theorem free_wired_multiOpen_eq_of_not_badP_q2
    (d : ℕ) (hd : 1 ≤ d)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hbad : p ∉ FK.fwa_badP d)
    (T : Finset (Sym2 (Lattice.Site d))) :
    (FK.freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.fmu_multiOpen T) =
    (FK.wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.fmu_multiOpen T) := by
  exact FK.fwa_multiOpen_agree hd hp hp1 hbad T


theorem free_wired_multiOpen_eq_of_beta_not_badP_q2
    (d : ℕ) (hd : 1 ≤ d)
    {β : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP d)
    (T : Finset (Sym2 (Lattice.Site d))) :
    (FK.freeInfiniteVolume d (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
      (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.fmu_multiOpen T) =
    (FK.wiredInfiniteVolume d (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
      (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.fmu_multiOpen T) :=
  free_wired_multiOpen_eq_of_not_badP_q2 d hd
    (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) hbad T


theorem free_wired_boxConnEvent_eq_of_not_badP_q2
    (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hbad : p ∉ FK.fwa_badP d)
    (x y : boxVerts d N) :
    (FK.freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxConnEvent d N x y) =
      (FK.wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxConnEvent d N x y) := by
  simpa [FK.boxConnEvent] using
    (FK.fwa_box_agree (d := d) hd hp hp1 hbad hN
      (FK.connEvent_isIncreasing (FK.boxGraph d N) x y))


theorem free_wired_boxConnEvent_eq_of_beta_not_badP_q2
    (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    {β : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP d)
    (x y : boxVerts d N) :
    (FK.freeInfiniteVolume d (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
        (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxConnEvent d N x y) =
      (FK.wiredInfiniteVolume d (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
        (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxConnEvent d N x y) :=
  free_wired_boxConnEvent_eq_of_not_badP_q2 d N hd hN
    (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) hbad x y


theorem freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
    {β : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    {n : ℕ} (hn : 1 ≤ n) :
    freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n =
      wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n :=
  free_wired_boxConnEvent_eq_of_beta_not_badP_q2 3 n (by norm_num) hn
    hβ hbad (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)


theorem wiredInfiniteVolumeXAxisConnection_eq_free_of_beta_not_badP_q2
    {β : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    {n : ℕ} (hn : 1 ≤ n) :
    wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n =
      freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n :=
  (freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
    hβ hbad hn).symm


theorem eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
    {β : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
    ∀ᶠ n in atTop,
      freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n =
        wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact
    freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
      hβ hbad hn


theorem
    eventually_wiredInfiniteVolumeXAxisConnection_eq_free_of_beta_not_badP_q2
    {β : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
    ∀ᶠ n in atTop,
      wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n =
        freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n :=
  (eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
    hβ hbad).mono fun _ hn => hn.symm


theorem freeXAxisWiredQ2ConnectionAgrees_of_free_not_badP
    {β : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβ) :
    FreeXAxisWiredQ2ConnectionAgrees β hβ := by
  unfold FreeXAxisQ2ConnectionAgrees FreeXAxisWiredQ2ConnectionAgrees at *
  filter_upwards
    [hfree, eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
      hβ hbad] with n hconn heq
  exact hconn.trans heq


theorem freeXAxisQ2ConnectionAgrees_of_wired_not_badP
    {β : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hwired : FreeXAxisWiredQ2ConnectionAgrees β hβ) :
    FreeXAxisQ2ConnectionAgrees β hβ := by
  unfold FreeXAxisQ2ConnectionAgrees FreeXAxisWiredQ2ConnectionAgrees at *
  filter_upwards
    [hwired, eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
      hβ hbad] with n hconn heq
  exact hconn.trans heq.symm


theorem plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree
    {β : ℝ} (hβpos : 0 < β) (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos) :
    PlusXAxisWiredQ2ConnectionAgrees β hβpos := by
  unfold FreeXAxisQ2ConnectionAgrees PlusXAxisWiredQ2ConnectionAgrees at *
  filter_upwards
    [hfree, eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
      hβpos hbad] with n hconn heq
  have htwo :
      twoPointOnXAxis β n = freeTwoPointOnXAxis β n := by
    simpa [twoPointOnXAxis, twoPointAtDisplacement, freeTwoPointOnXAxis,
      freeTwoPointAtDisplacement] using
        hagree β hβc ising3DOrigin (ising3DXAxisRay n)
  calc
    |twoPointOnXAxis β n| = |freeTwoPointOnXAxis β n| := by rw [htwo]
    _ = freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n := hconn
    _ = wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n := heq


theorem
    fkXAxisConnectionExactExponentialDecay_freeInfiniteVolumeQ2_iff_wired
    {β A m : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
    FKXAxisConnectionExactExponentialDecay
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m ↔
    FKXAxisConnectionExactExponentialDecay
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m :=
  FKXAxisConnectionExactExponentialDecay.congr_eventually_iff
    ((eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
      hβ hbad).mono fun _ hn => hn.symm)


theorem
    fkXAxisConnectionExactExponentialDecay_wiredInfiniteVolumeQ2_iff_free
    {β A m : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
    FKXAxisConnectionExactExponentialDecay
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m ↔
    FKXAxisConnectionExactExponentialDecay
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m :=
  (fkXAxisConnectionExactExponentialDecay_freeInfiniteVolumeQ2_iff_wired
    hβ hbad).symm


theorem
    fkXAxisConnectionSubexponentialPrefactorDecay_freeInfiniteVolumeQ2_iff_wired
    {β m : ℝ} {A : ℕ → ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
    FKXAxisConnectionSubexponentialPrefactorDecay
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m ↔
    FKXAxisConnectionSubexponentialPrefactorDecay
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m :=
  FKXAxisConnectionSubexponentialPrefactorDecay.congr_eventually_iff
    ((eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
      hβ hbad).mono fun _ hn => hn.symm)


theorem
    fkXAxisConnectionSubexponentialPrefactorDecay_wiredInfiniteVolumeQ2_iff_free
    {β m : ℝ} {A : ℕ → ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
    FKXAxisConnectionSubexponentialPrefactorDecay
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m ↔
    FKXAxisConnectionSubexponentialPrefactorDecay
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m :=
  (fkXAxisConnectionSubexponentialPrefactorDecay_freeInfiniteVolumeQ2_iff_wired
    hβ hbad).symm


theorem
    fkXAxisConnectionTwoSidedSubexponentialBounds_freeInfiniteVolumeQ2_iff_wired
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo Ahi m ↔
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo Ahi m :=
  FKXAxisConnectionTwoSidedSubexponentialBounds.congr_eventually_iff
    ((eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
      hβ hbad).mono fun _ hn => hn.symm)


theorem
    fkXAxisConnectionTwoSidedSubexponentialBounds_wiredInfiniteVolumeQ2_iff_free
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo Ahi m ↔
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo Ahi m :=
  (fkXAxisConnectionTwoSidedSubexponentialBounds_freeInfiniteVolumeQ2_iff_wired
    hβ hbad).symm


theorem
    free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
    {β A m : ℝ} (hβpos : 0 < β) (hA : 0 < A)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionExactExponentialDecay
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m :=
  free_hasInverseCorrelationLength_xAxis_of_exactExponential hA
    (freeXAxisExactExponentialDecay_of_fkConnectionComparison hfree hconn)


theorem
    plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
    {β A m : ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hA : 0 < A)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionExactExponentialDecay
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m :=
  plus_hasInverseCorrelationLength_xAxis_of_free_agree hagree hβc
    (free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
      hβpos hA hfree hconn)


theorem
    free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionSubexponentialPrefactorDecay
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m :=
  free_hasInverseCorrelationLength_xAxis_of_subexponentialPrefactor
    (freeXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison
      hfree hconn)


theorem
    plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionSubexponentialPrefactorDecay
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m :=
  plus_hasInverseCorrelationLength_xAxis_of_free_agree hagree hβc
    (free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
      hβpos hfree hconn)


theorem
    free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m :=
  free_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds
    (freeXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison
      hfree hconn)


theorem
    plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m :=
  plus_hasInverseCorrelationLength_xAxis_of_free_agree hagree hβc
    (free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
      hβpos hfree hconn)


theorem
    free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential
    {β A m : ℝ} (hβpos : 0 < β) (hA : 0 < A)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionExactExponentialDecay
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m :=
  free_hasInverseCorrelationLength_xAxis_of_exactExponential hA
    (freeXAxisExactExponentialDecay_of_fkConnectionComparison
      (freeXAxisWiredQ2ConnectionAgrees_of_free_not_badP
        hβpos hbad hfree)
      hconn)


theorem
    plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential
    {β A m : ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hA : 0 < A)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionExactExponentialDecay
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m :=
  plus_hasInverseCorrelationLength_xAxis_of_exactExponential hA
    (plusXAxisExactExponentialDecay_of_fkConnectionComparison
      (plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree
        hβpos hβc hagree hbad hfree)
      hconn)


theorem
    free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionSubexponentialPrefactorDecay
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m :=
  free_hasInverseCorrelationLength_xAxis_of_subexponentialPrefactor
    (freeXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison
      (freeXAxisWiredQ2ConnectionAgrees_of_free_not_badP
        hβpos hbad hfree)
      hconn)


theorem
    plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionSubexponentialPrefactorDecay
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m :=
  plus_hasInverseCorrelationLength_xAxis_of_subexponentialPrefactor
    (plusXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison
      (plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree
        hβpos hβc hagree hbad hfree)
      hconn)


theorem
    free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m :=
  free_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds
    (freeXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison
      (freeXAxisWiredQ2ConnectionAgrees_of_free_not_badP
        hβpos hbad hfree)
      hconn)


theorem
    plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m :=
  plus_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds
    (plusXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison
      (plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree
        hβpos hβc hagree hbad hfree)
      hconn)


theorem
    free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
    {β A m : ℝ} (hβpos : 0 < β) (hA : 0 < A) (hm : 0 < m)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionExactExponentialDecay
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
    hβpos hA hfree hconn).hasCorrelationLength_inv hm


theorem
    plus_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
    {β A m : ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hA : 0 < A) (hm : 0 < m)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionExactExponentialDecay
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
    hβpos hβc hA hagree hfree hconn).hasCorrelationLength_inv hm


theorem
    free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β) (hm : 0 < m)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionSubexponentialPrefactorDecay
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
    hβpos hfree hconn).hasCorrelationLength_inv hm


theorem
    plus_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hm : 0 < m)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionSubexponentialPrefactorDecay
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
    hβpos hβc hagree hfree hconn).hasCorrelationLength_inv hm


theorem
    free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β) (hm : 0 < m)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
    hβpos hfree hconn).hasCorrelationLength_inv hm


theorem
    plus_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hm : 0 < m)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
    hβpos hβc hagree hfree hconn).hasCorrelationLength_inv hm


theorem
    free_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential
    {β A m : ℝ} (hβpos : 0 < β) (hA : 0 < A) (hm : 0 < m)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionExactExponentialDecay
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential
    hβpos hA hbad hfree hconn).hasCorrelationLength_inv hm


theorem
    free_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β) (hm : 0 < m)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionSubexponentialPrefactorDecay
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor
    hβpos hbad hfree hconn).hasCorrelationLength_inv hm


theorem
    free_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β) (hm : 0 < m)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided
    hβpos hbad hfree hconn).hasCorrelationLength_inv hm


theorem plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential
    {β A m : ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hA : 0 < A) (hm : 0 < m)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionExactExponentialDecay
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  plus_hasCorrelationLength_xAxis_of_exactExponential hA hm
    (plusXAxisExactExponentialDecay_of_fkConnectionComparison
      (plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree
        hβpos hβc hagree hbad hfree)
      hconn)


theorem plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hm : 0 < m)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionSubexponentialPrefactorDecay
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  plus_hasCorrelationLength_xAxis_of_subexponentialPrefactor hm
    (plusXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison
      (plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree
        hβpos hβc hagree hbad hfree)
      hconn)


theorem
    plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSidedSubexponentialBounds
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hm : 0 < m)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  plus_hasCorrelationLength_xAxis_of_twoSidedSubexponentialBounds hm
    (plusXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison
      (plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree
        hβpos hβc hagree hbad hfree)
      hconn)


theorem
    free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential
    {β A mass : ℝ} (hβpos : 0 < β) (hA : 0 < A)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hexact : FreeFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass :=
  free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
    hβpos hA hfree
    (fkExactFreeIVQ2_of_freeFiniteVolumeExactOfBeta hβpos hexact)


theorem
    plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential
    {β A mass : ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hA : 0 < A)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hexact : FreeFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass :=
  plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
    hβpos hβc hA hagree hfree
    (fkExactFreeIVQ2_of_freeFiniteVolumeExactOfBeta hβpos hexact)


theorem
    free_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential
    {β A mass : ℝ} (hβpos : 0 < β) (hA : 0 < A)
    (hmass : 0 < mass)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hexact : FreeFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential
    hβpos hA hfree hexact).hasCorrelationLength_inv hmass


theorem
    plus_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential
    {β A mass : ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hA : 0 < A) (hmass : 0 < mass)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hexact : FreeFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential
    hβpos hβc hA hagree hfree hexact).hasCorrelationLength_inv hmass


theorem
    free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hsubexp :
      FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass :=
  free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
    hβpos hfree
    (fkSubexpFreeIVQ2_of_freeFiniteVolumeSubexpOfBeta hβpos hsubexp)


theorem
    plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hsubexp :
      FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass :=
  plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
    hβpos hβc hagree hfree
    (fkSubexpFreeIVQ2_of_freeFiniteVolumeSubexpOfBeta hβpos hsubexp)


theorem
    free_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hmass : 0 < mass)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hsubexp :
      FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor
    hβpos hfree hsubexp).hasCorrelationLength_inv hmass


theorem
    plus_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hmass : 0 < mass)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hsubexp :
      FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor
    hβpos hβc hagree hfree hsubexp).hasCorrelationLength_inv hmass


theorem
    free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential
    {β A mass : ℝ} (hβpos : 0 < β) (hA : 0 < A)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hexact : WiredFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass :=
  free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential
    hβpos hA hbad hfree
    (fkExactWiredIVQ2_of_wiredFiniteVolumeExactOfBeta hβpos hexact)


theorem
    plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential
    {β A mass : ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hA : 0 < A)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hexact : WiredFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass :=
  plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential
    hβpos hβc hA hagree hbad hfree
    (fkExactWiredIVQ2_of_wiredFiniteVolumeExactOfBeta hβpos hexact)


theorem
    free_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential
    {β A mass : ℝ} (hβpos : 0 < β) (hA : 0 < A)
    (hmass : 0 < mass)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hexact : WiredFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential
    hβpos hA hbad hfree hexact).hasCorrelationLength_inv hmass


theorem
    plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential
    {β A mass : ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hA : 0 < A) (hmass : 0 < mass)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hexact : WiredFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential
    hβpos hβc hA hagree hbad hfree hexact).hasCorrelationLength_inv hmass


theorem
    free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hsubexp :
      WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass :=
  free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor
    hβpos hbad hfree
    (fkSubexpWiredIVQ2_of_wiredFiniteVolumeSubexpOfBeta hβpos hsubexp)


theorem
    plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hsubexp :
      WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass :=
  plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor
    hβpos hβc hagree hbad hfree
    (fkSubexpWiredIVQ2_of_wiredFiniteVolumeSubexpOfBeta hβpos hsubexp)


theorem
    free_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hmass : 0 < mass)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hsubexp :
      WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor
    hβpos hbad hfree hsubexp).hasCorrelationLength_inv hmass


theorem
    plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hmass : 0 < mass)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hsubexp :
      WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor
    hβpos hβc hagree hbad hfree hsubexp).hasCorrelationLength_inv hmass


theorem
    free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hbounds :
      FreeFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass :=
  free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
    hβpos hfree
    (fkTwoSidedFreeIVQ2_of_freeFiniteVolumeBoundsOfBeta hβpos hbounds)


theorem
    plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hbounds :
      FreeFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass :=
  plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
    hβpos hβc hagree hfree
    (fkTwoSidedFreeIVQ2_of_freeFiniteVolumeBoundsOfBeta hβpos hbounds)


theorem
    free_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hmass : 0 < mass)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hbounds :
      FreeFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided
    hβpos hfree hbounds).hasCorrelationLength_inv hmass


theorem
    plus_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hmass : 0 < mass)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hbounds :
      FreeFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided
    hβpos hβc hagree hfree hbounds).hasCorrelationLength_inv hmass


theorem
    free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hbounds :
      WiredFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass :=
  free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided
    hβpos hbad hfree
    (fkTwoSidedWiredIVQ2_of_wiredFiniteVolumeBoundsOfBeta hβpos hbounds)


theorem
    plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hbounds :
      WiredFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass :=
  plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided
    hβpos hβc hagree hbad hfree
    (fkTwoSidedWiredIVQ2_of_wiredFiniteVolumeBoundsOfBeta hβpos hbounds)


theorem
    free_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hmass : 0 < mass)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hbounds :
      WiredFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided
    hβpos hbad hfree hbounds).hasCorrelationLength_inv hmass


theorem
    plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hmass : 0 < mass)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hbounds :
      WiredFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided
    hβpos hβc hagree hbad hfree hbounds).hasCorrelationLength_inv hmass


theorem
    plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSidedSubexpBounds
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) (hmass : 0 < mass)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hlo_log :
      Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        atTop (nhds 0))
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hlo :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        Alo n * Real.exp (-(mass * (n : ℝ))) ≤
          (wiredFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos)
            (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (boxConnEvent 3 n (ising3DOriginBoxVertex n)
                (ising3DXAxisBoxVertex n)))
    (hhi :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        (wiredFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos)
          (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) ≤
          Ahi n * Real.exp (-(mass * (n : ℝ)))) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSidedSubexponentialBounds
    hβpos hβc hmass hagree hbad hfree
    (fkTwoSidedWiredIVQ2_of_eventually_boxConnEvent_bounds
      (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
      hlo_pos hhi_pos hlo_log hhi_log hlo hhi)

end Exact3D
end StatMech
