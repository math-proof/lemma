/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.ABThermodynamicPassage
import Def.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part13
open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}


variable {W : Type*}


section Marginals

variable [Countable V]


omit [Countable V] in

theorem abigWindowMag_le_envelope [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (o x : S) (beta h : Real) :
    abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) x beta h <=
      abigWindowEnvelope G J S o beta h := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩


theorem abigWindowEnvelope_monotoneOn_beta [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (o : S) (h : Real)
    (hJ : forall e, 0 <= J e) (hh : 0 <= h) :
    MonotoneOn (fun beta => abigWindowEnvelope G J S o beta h) (Ici 0) := by
  intro beta hbeta gamma hgamma hbg
  unfold abigWindowEnvelope
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  calc
    abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) x beta h <=
        abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) x gamma h := by
      apply abfaMag_monotoneOn_beta
        (abigWindowGraph G S) (abigWindowCoupling J S) x h
      · intro e he
        induction e using Sym2.inductionOn with
        | _ a b => simpa using hJ s((a : V), (b : V))
      · exact hh
      · exact hbeta
      · exact hgamma
      · exact hbg
    _ <= _ := abigWindowMag_le_envelope G J S o x gamma h


theorem abigWindowEnvelope_monotoneOn_field [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (o : S) (beta : Real)
    (hJ : forall e, 0 <= J e) (hbeta : 0 <= beta) :
    MonotoneOn (fun h => abigWindowEnvelope G J S o beta h) (Ici 0) := by
  intro h hh t ht hht
  unfold abigWindowEnvelope
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  calc
    abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) x beta h <=
        abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) x beta t := by
      apply abfaMag_monotoneOn_field
        (abigWindowGraph G S) (abigWindowCoupling J S) x beta
      · intro e he
        induction e using Sym2.inductionOn with
        | _ a b => simpa using hJ s((a : V), (b : V))
      · exact hbeta
      · exact hh
      · exact ht
      · exact hht
    _ <= _ := abigWindowMag_le_envelope G J S o x beta t


theorem abig_window_aizenmanBarsky_finiteEnvelope [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (o : S) (beta h J0 : Real)
    (hbeta : 0 <= beta) (hh : 0 <= h) (hJ : forall e, 0 <= J e)
    (hrow : forall x : S,
      abcrIncidentCoupling (abigWindowGraph G S)
        (abigWindowCoupling J S) x <= J0) :
    deriv (fun b =>
      abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) o b h) beta <=
      J0 * abigWindowEnvelope G J S o beta h *
        deriv (fun t =>
          abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) o beta t) h := by
  have hJwin : ∀ e, e ∈ (abigWindowGraph G S).edgeFinset →
      0 <= abigWindowCoupling J S e := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y => simpa using hJ s((x : V), (y : V))
  have hp := abfaParams_mem (abigWindowGraph G S)
    (abigWindowCoupling J S) hJwin beta h hbeta hh
  have hU : 0 <= abigWindowEnvelope G J S o beta h := by
    exact (abgi_probV_nonneg
      (abfaParams (abigWindowGraph G S) (abigWindowCoupling J S) beta h)
      hp _).trans (abigWindowMag_le_envelope G J S o o beta h)
  apply abfa_aizenmanBarsky_le_envelope
    (abigWindowGraph G S) (abigWindowCoupling J S) o beta h J0
    (abigWindowEnvelope G J S o beta h)
  · exact hJwin
  · exact hrow
  · exact hbeta
  · exact hh
  · exact hU
  · intro x
    exact abigWindowMag_le_envelope G J S o x beta h


theorem abigWindowEnvelope_le_mag [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (o : S) (beta h : Real)
    (hbeta : 0 <= beta) (hh : 0 <= h) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (hInfiniteTarget : forall x : S,
      abigMag G J (x : V) beta h <= abigMag G J (o : V) beta h) :
    abigWindowEnvelope G J S o beta h <= abigMag G J (o : V) beta h := by
  unfold abigWindowEnvelope
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  rw [abig_abfaMag_eq_finiteConn G J S x beta h
    hbeta hh hJ hJsupport]
  apply le_trans ?_ (hInfiniteTarget x)
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  exact abig_connEvent_mono_set (withGhost G) (Set.subset_univ _)
    (some (x : V)) none


theorem abig_window_aizenmanBarsky [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (o : S) (beta h J0 : Real)
    (hbeta : 0 <= beta) (hh : 0 <= h) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (hrow : forall x : S,
      abcrIncidentCoupling (abigWindowGraph G S)
        (abigWindowCoupling J S) x <= J0)
    (hInfiniteTarget : forall x : S,
      abigMag G J (x : V) beta h <= abigMag G J (o : V) beta h) :
    deriv (fun b =>
      abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) o b h) beta <=
      J0 * abigMag G J (o : V) beta h *
        deriv (fun t =>
          abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) o beta t) h := by
  apply abfa_aizenmanBarsky_le_envelope
    (abigWindowGraph G S) (abigWindowCoupling J S) o beta h J0
    (abigMag G J (o : V) beta h)
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y => simpa using hJ s((x : V), (y : V))
  · exact hrow
  · exact hbeta
  · exact hh
  · exact abigMag_nonneg G J (o : V) beta h
  · intro x
    change abfaMag (abigWindowGraph G S) (abigWindowCoupling J S)
      x beta h <= abigMag G J (o : V) beta h
    rw [abig_abfaMag_eq_finiteConn G J S x beta h
      hbeta hh hJ hJsupport]
    apply le_trans ?_ (hInfiniteTarget x)
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    exact abig_connEvent_mono_set (withGhost G) (Set.subset_univ _)
      (some (x : V)) none


theorem abig_tendsto_mag_exhaustion [DecidableEq V]
    (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (T : Nat -> Finset (Option V)) (hmono : Monotone T)
    (hcover : forall F : Finset (Option V), exists n, F ⊆ T n) :
    Tendsto
      (fun n => (abigMeasure J beta h).real
        (connEvent (withGhost G) (T n : Set (Option V)) (some o) {none}))
      atTop (nhds (abigMag G J o beta h)) := by
  simpa [abigMag] using
    (abig_tendsto_real_connEvent_exhaustion (abigMeasure J beta h)
      (withGhost G) T (some o) none hmono hcover)


theorem abig_tendsto_abfaMag_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (hbeta : 0 <= beta) (hh : 0 <= h) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hmono : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n)) :
    Tendsto
      (fun n => abfaMag (abigWindowGraph G (S n))
        (abigWindowCoupling J (S n)) ⟨o, ho n⟩ beta h)
      atTop (nhds (abigMag G J o beta h)) := by
  apply Filter.Tendsto.congr'
    (Filter.Eventually.of_forall (fun n =>
      (abig_abfaMag_eq_finiteConn G J (S n) ⟨o, ho n⟩ beta h
        hbeta hh hJ hJsupport).symm))
  exact abig_tendsto_mag_exhaustion G J o beta h
    (fun n => abigGhostWindow (S n)) hmono hcover


theorem abigMag_monotoneOn_field_of_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (beta : Real) (hbeta : 0 <= beta)
    (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n)) :
    MonotoneOn (fun h => abigMag G J o beta h) (Ici 0) := by
  intro h1 hh1 h2 hh2 h12
  apply le_of_tendsto_of_tendsto
    (abig_tendsto_abfaMag_exhaustion G J o beta h1 hbeta hh1 hJ hJsupport
      S ho hmonoWindow hcover)
    (abig_tendsto_abfaMag_exhaustion G J o beta h2 hbeta hh2 hJ hJsupport
      S ho hmonoWindow hcover)
  exact Filter.Eventually.of_forall (fun n => by
    apply abfaMag_monotoneOn_field
      (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
        ⟨o, ho n⟩ beta
    · intro e he
      induction e using Sym2.inductionOn with
      | _ x y => simpa using hJ s((x : V), (y : V))
    · exact hbeta
    · exact hh1
    · exact hh2
    · exact h12)


theorem abigMag_continuousAt_field_of_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (hbeta : 0 <= beta) (hh : 0 < h)
    (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n)) :
    ContinuousAt (fun t => abigMag G J o beta t) h := by
  let Mn : Nat -> Real -> Real := fun n t =>
    abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
      ⟨o, ho n⟩ beta t
  have hJwin : forall (n : Nat) (e : Sym2 (S n)),
      e ∈ (abigWindowGraph G (S n)).edgeFinset ->
        0 <= abigWindowCoupling J (S n) e := by
    intro n e he
    induction e using Sym2.inductionOn with
    | _ x y => simpa using hJ s((x : V), (y : V))
  have hlocal : forall t, |t - h| < h / 2 ->
      |abigMag G J o beta t - abigMag G J o beta h| <=
        (2 / h) * |t - h| := by
    intro t ht
    have htpos : 0 < t := by
      have hlower : h - t <= |t - h| := by
        rw [abs_sub_comm]
        exact le_abs_self (h - t)
      linarith
    have hfinite : forall n,
        |Mn n t - Mn n h| <= (2 / h) * |t - h| := by
      intro n
      have hderiv : forall (u : Real), u ∈ Set.uIcc h t ->
          ‖deriv (Mn n) u‖ <= 2 / h := by
        intro u hu
        have hudist : |u - h| <= |t - h| := abs_sub_left_of_mem_uIcc hu
        have hupos : 0 < u := by
          have hlower : h - u <= |u - h| := by
            rw [abs_sub_comm]
            exact le_abs_self (h - u)
          linarith
        have hnonneg : 0 <= deriv (Mn n) u := by
          apply abfa_deriv_field_nonneg
            (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
              ⟨o, ho n⟩ beta u (hJwin n) hbeta hupos.le
        have hupper : deriv (Mn n) u <= 1 / u := by
          exact abgr_deriv_abfaMag_field_le
            (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
              (hJwin n) ⟨o, ho n⟩ beta u hbeta hupos
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        exact hupper.trans ((div_le_div_iff₀ hupos hh).mpr (by
          have : h <= 2 * u := by
            have hlower : h - u <= |u - h| := by
              rw [abs_sub_comm]
              exact le_abs_self (h - u)
            linarith
          simpa using this))
      have hmvt := (convex_uIcc h t).norm_image_sub_le_of_norm_deriv_le
        (f := Mn n) (C := 2 / h)
        (fun u _ => (abgr_hasDerivAt_abfaMag_field
          (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            ⟨o, ho n⟩ beta u).differentiableAt)
        hderiv left_mem_uIcc right_mem_uIcc
      simpa [Real.norm_eq_abs] using hmvt
    have htend : Tendsto (fun n => |Mn n t - Mn n h|) atTop
        (nhds |abigMag G J o beta t - abigMag G J o beta h|) :=
      ((abig_tendsto_abfaMag_exhaustion G J o beta t hbeta htpos.le hJ hJsupport
          S ho hmonoWindow hcover).sub
        (abig_tendsto_abfaMag_exhaustion G J o beta h hbeta hh.le hJ hJsupport
          S ho hmonoWindow hcover)).abs
    exact le_of_tendsto htend (Filter.Eventually.of_forall hfinite)
  rw [Metric.continuousAt_iff]
  intro epsilon hepsilon
  refine ⟨min (h / 2) (epsilon * h / 2), by positivity, ?_⟩
  intro t hdist
  rw [Real.dist_eq] at hdist ⊢
  have ht : |t - h| < h / 2 :=
    lt_of_lt_of_le hdist (min_le_left _ _)
  calc
    |abigMag G J o beta t - abigMag G J o beta h| <=
        (2 / h) * |t - h| := hlocal t ht
    _ < (2 / h) * (epsilon * h / 2) := by
      apply mul_lt_mul_of_pos_left
      · exact lt_of_lt_of_le hdist (min_le_right _ _)
      · positivity
    _ = epsilon := by field_simp


theorem abigMag_differentiableAt_field_of_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (hbeta : 0 <= beta) (hh : 0 < h)
    (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n)) :
    DifferentiableAt Real (fun t => abigMag G J o beta t) h := by
  let Mn : Nat -> Real -> Real := fun n t =>
    abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
      ⟨o, ho n⟩ beta t
  let dn : Nat -> Real := fun n => deriv (Mn n) h
  have hJwin : forall (n : Nat) (e : Sym2 (S n)),
      e ∈ (abigWindowGraph G (S n)).edgeFinset ->
        0 <= abigWindowCoupling J (S n) e := by
    intro n e he
    induction e using Sym2.inductionOn with
    | _ x y => simpa using hJ s((x : V), (y : V))
  have hlim : forall y, |y - h| < h / 2 ->
      Tendsto (fun n => Mn n y) atTop (nhds (abigMag G J o beta y)) := by
    intro y hy
    have hypos : 0 < y := by
      have hlower : h - y <= |y - h| := by
        rw [abs_sub_comm]
        exact le_abs_self (h - y)
      linarith
    exact abig_tendsto_abfaMag_exhaustion G J o beta y hbeta hypos.le
      hJ hJsupport S ho hmonoWindow hcover
  have htaylor : forall n y, |y - h| < h / 2 ->
      |Mn n y - Mn n h - dn n * (y - h)| <=
        (8 / h ^ 2) * |y - h| ^ 2 := by
    intro n y hy
    have hpos_on : forall (z : Real), z ∈ Set.uIcc h y -> 0 < z := by
      intro z hz
      have hzdist : |z - h| <= |y - h| := abs_sub_left_of_mem_uIcc hz
      have hlower : h - z <= |z - h| := by
        rw [abs_sub_comm]
        exact le_abs_self (h - z)
      linarith
    apply abgr_taylor_remainder_le (Mn n) h y (8 / h ^ 2) (by positivity)
    · intro z hz
      exact (abgr_hasDerivAt_abfaMag_field
        (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
          ⟨o, ho n⟩ beta z).differentiableAt
    · intro z hz
      exact (abgr_hasDerivAt_deriv_abfaMag_field
        (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
          ⟨o, ho n⟩ beta z).differentiableAt
    · intro z hz
      have hzpos := hpos_on z hz
      have hsecond := abgr_abs_deriv_deriv_abfaMag_field_le
        (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
          (hJwin n) ⟨o, ho n⟩ beta z hbeta hzpos
      exact hsecond.trans ((div_le_div_iff₀ (sq_pos_of_pos hzpos)
        (sq_pos_of_pos hh)).mpr (by
          have hzdist : |z - h| <= |y - h| := abs_sub_left_of_mem_uIcc hz
          have hlower : h - z <= |z - h| := by
            rw [abs_sub_comm]
            exact le_abs_self (h - z)
          have hzhalf : h / 2 < z := by linarith
          nlinarith [sq_nonneg (2 * z - h)]))
  obtain ⟨L, hL⟩ := abgr_hasDerivAt_limit_of_taylor Mn
    (fun t => abigMag G J o beta t) dn h (h / 2) (8 / h ^ 2)
      (by linarith) (by positivity) hlim htaylor
  exact hL.differentiableAt


theorem abigMag_beta_lipschitz_of_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 beta gamma h : Real)
    (hJ0 : 0 <= J0) (hbeta : 0 <= beta) (hgamma : 0 <= gamma)
    (hh : 0 < h) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hrow : forall n (x : S n),
      abcrIncidentCoupling (abigWindowGraph G (S n))
        (abigWindowCoupling J (S n)) x <= J0)
    (hInfiniteTarget : forall b t, 0 <= b -> 0 <= t ->
      forall n (x : S n),
        abigMag G J (x : V) b t <= abigMag G J o b t)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n)) :
    |abigMag G J o gamma h - abigMag G J o beta h| <=
      (J0 / h) * |gamma - beta| := by
  let Mn : Nat -> Real -> Real := fun n b =>
    abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
      ⟨o, ho n⟩ b h
  let Cn : Nat -> Real -> Real := fun n b =>
    abigWindowEnvelope G J (S n) ⟨o, ho n⟩ b h
  have hJwin : forall (n : Nat) (e : Sym2 (S n)),
      e ∈ (abigWindowGraph G (S n)).edgeFinset ->
        0 <= abigWindowCoupling J (S n) e := by
    intro n e he
    induction e using Sym2.inductionOn with
    | _ x y => simpa using hJ s((x : V), (y : V))
  have hfinite : forall n,
      |Mn n gamma - Mn n beta| <= (J0 / h) * |gamma - beta| := by
    intro n
    have hderiv : forall (b : Real), b ∈ Set.uIcc beta gamma ->
        ‖deriv (Mn n) b‖ <= J0 / h := by
      intro b hb
      have hb0 : 0 <= b := by
        rw [Set.mem_uIcc] at hb
        rcases hb with hb | hb <;> linarith
      have hbetaNN : 0 <= deriv (Mn n) b := by
        apply abfa_deriv_beta_nonneg
          (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            ⟨o, ho n⟩ b h (hJwin n) hb0 hh.le
      have hAB := abig_window_aizenmanBarsky_finiteEnvelope
        G J (S n) ⟨o, ho n⟩ b h J0 hb0 hh.le hJ (hrow n)
      change deriv (Mn n) b <=
        J0 * Cn n b * deriv (fun t =>
          abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            ⟨o, ho n⟩ b t) h at hAB
      have hCn1 : Cn n b <= 1 := by
        calc
          Cn n b <= abigMag G J o b h :=
            abigWindowEnvelope_le_mag G J (S n) ⟨o, ho n⟩ b h
              hb0 hh.le hJ hJsupport (hInfiniteTarget b h hb0 hh.le n)
          _ <= 1 := measureReal_le_one
      have hfield0 : 0 <= deriv (fun t =>
          abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            ⟨o, ho n⟩ b t) h :=
        abfa_deriv_field_nonneg
          (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            ⟨o, ho n⟩ b h (hJwin n) hb0 hh.le
      have hfield1 : deriv (fun t =>
          abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            ⟨o, ho n⟩ b t) h <= 1 / h :=
        abgr_deriv_abfaMag_field_le
          (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            (hJwin n) ⟨o, ho n⟩ b h hb0 hh
      rw [Real.norm_eq_abs, abs_of_nonneg hbetaNN]
      calc
        deriv (Mn n) b <= J0 * Cn n b * deriv (fun t =>
            abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
              ⟨o, ho n⟩ b t) h := hAB
        _ <= J0 * 1 * deriv (fun t =>
            abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
              ⟨o, ho n⟩ b t) h :=
          by
            simpa [mul_assoc] using
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hCn1 hfield0) hJ0)
        _ <= J0 * (1 / h) := by
          simpa using mul_le_mul_of_nonneg_left hfield1 hJ0
        _ = J0 / h := by ring
    have hmvt := (convex_uIcc beta gamma).norm_image_sub_le_of_norm_deriv_le
      (f := Mn n) (C := J0 / h)
      (fun b _ => by
        change DifferentiableAt Real (fun u =>
          abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            ⟨o, ho n⟩ u h) b
        have hjoint := abfa_differentiableAt_mag_joint
          (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            ⟨o, ho n⟩ b h
        have hpair : DifferentiableAt Real (fun u : Real => (u, h)) b :=
          differentiableAt_id.prodMk (differentiableAt_const h)
        have hc := DifferentiableAt.comp (f := fun u : Real => (u, h))
          (g := Function.uncurry (abfaMag (abigWindowGraph G (S n))
            (abigWindowCoupling J (S n)) ⟨o, ho n⟩)) b hjoint hpair
        simpa [Function.comp_def] using hc)
      hderiv left_mem_uIcc right_mem_uIcc
    simpa [Real.norm_eq_abs] using hmvt
  have htend : Tendsto (fun n => |Mn n gamma - Mn n beta|) atTop
      (nhds |abigMag G J o gamma h - abigMag G J o beta h|) :=
    ((abig_tendsto_abfaMag_exhaustion G J o gamma h hgamma hh.le hJ hJsupport
        S ho hmonoWindow hcover).sub
      (abig_tendsto_abfaMag_exhaustion G J o beta h hbeta hh.le hJ hJsupport
        S ho hmonoWindow hcover)).abs
  exact le_of_tendsto htend (Filter.Eventually.of_forall hfinite)


theorem abigMag_continuousAt_joint_of_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 beta h : Real)
    (hJ0 : 0 <= J0) (hbeta : 0 <= beta) (hh : 0 < h)
    (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hrow : forall n (x : S n),
      abcrIncidentCoupling (abigWindowGraph G (S n))
        (abigWindowCoupling J (S n)) x <= J0)
    (hInfiniteTarget : forall b t, 0 <= b -> 0 <= t ->
      forall n (x : S n),
        abigMag G J (x : V) b t <= abigMag G J o b t)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n)) :
    ContinuousAt (Function.uncurry (abigMag G J o)) (beta, h) := by
  have hfield := abigMag_continuousAt_field_of_exhaustion
    G J o beta h hbeta hh hJ hJsupport S ho hmonoWindow hcover
  rw [Metric.continuousAt_iff] at hfield ⊢
  intro epsilon hepsilon
  obtain ⟨deltaField, hdeltaField, hfieldBound⟩ :=
    hfield (epsilon / 2) (by linarith)
  let deltaBeta : Real := epsilon * h / (4 * (J0 + 1))
  have hdeltaBeta : 0 < deltaBeta := by
    dsimp [deltaBeta]
    positivity
  refine ⟨min (h / 2) (min deltaField deltaBeta), by positivity, ?_⟩
  intro z hz
  have hzbeta : dist z.1 beta <= dist z (beta, h) := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hzfield : dist z.2 h <= dist z (beta, h) := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have htclose : dist z.2 h < h / 2 :=
    lt_of_le_of_lt hzfield (lt_of_lt_of_le hz (min_le_left _ _))
  have htpos : 0 < z.2 := by
    rw [Real.dist_eq] at htclose
    have hlower : h - z.2 <= |z.2 - h| := by
      rw [abs_sub_comm]
      exact le_abs_self (h - z.2)
    linarith
  have hfieldClose :
      dist (abigMag G J o beta z.2) (abigMag G J o beta h) < epsilon / 2 := by
    apply hfieldBound
    exact lt_of_le_of_lt hzfield
      (lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _)))
  let b : Real := max z.1 0
  have hb0 : 0 <= b := le_max_right _ _
  have hbclose : |b - beta| <= dist z (beta, h) := by
    calc
      |b - beta| = |max z.1 0 - max beta 0| := by
        rw [max_eq_left hbeta]
      _ <= |z.1 - beta| := abs_max_sub_max_le_abs _ _ _
      _ = dist z.1 beta := by rw [Real.dist_eq]
      _ <= dist z (beta, h) := hzbeta
  have hbetaLip := abigMag_beta_lipschitz_of_exhaustion
    G J o J0 beta b z.2 hJ0 hbeta hb0 htpos hJ hJsupport
      S ho hrow hInfiniteTarget hmonoWindow hcover
  have hcoef : J0 / z.2 <= 2 * J0 / h := by
    have hhalf : h <= 2 * z.2 := by
      rw [Real.dist_eq] at htclose
      have hlower : h - z.2 <= |z.2 - h| := by
        rw [abs_sub_comm]
        exact le_abs_self (h - z.2)
      linarith
    rw [div_le_div_iff₀ htpos hh]
    nlinarith
  have hbetaClose :
      |abigMag G J o z.1 z.2 - abigMag G J o beta z.2| < epsilon / 2 := by
    rw [abigMag_eq_max_beta_zero G J o z.1 z.2 hJ]
    calc
      |abigMag G J o b z.2 - abigMag G J o beta z.2| <=
          (J0 / z.2) * |b - beta| := hbetaLip
      _ <= (2 * J0 / h) * dist z (beta, h) := by
        exact mul_le_mul hcoef hbclose (abs_nonneg _) (by positivity)
      _ <= (2 * J0 / h) * deltaBeta := by
        apply mul_le_mul_of_nonneg_left
        · exact le_of_lt (lt_of_lt_of_le hz
            (le_trans (min_le_right _ _) (min_le_right _ _)))
        · positivity
      _ < epsilon / 2 := by
        dsimp [deltaBeta]
        have hratio : J0 / (J0 + 1) < 1 := by
          apply (div_lt_one (by linarith)).mpr
          linarith
        have hratio0 : 0 <= J0 / (J0 + 1) := div_nonneg hJ0 (by linarith)
        field_simp
        nlinarith
  rw [Real.dist_eq] at hfieldClose ⊢
  exact (abs_sub_le (abigMag G J o z.1 z.2)
    (abigMag G J o beta z.2) (abigMag G J o beta h)).trans_lt (by
      linarith)


theorem abigMag_deriv_field_nonneg_of_monotone
    (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (hh : 0 < h)
    (hmono : MonotoneOn (fun t => abigMag G J o beta t) (Ici 0))
    (hdiff : DifferentiableAt Real (fun t => abigMag G J o beta t) h) :
    0 <= deriv (fun t => abigMag G J o beta t) h := by
  apply ge_of_tendsto hdiff.hasDerivAt.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have hinc : abigMag G J o beta h <= abigMag G J o beta (h + t) :=
    hmono (mem_Ici.mpr hh.le) (mem_Ici.mpr (by linarith [hh, ht]))
      (by linarith [ht])
  exact mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr hinc)

omit [Countable V] in


theorem abig_finiteMag_le [DecidableEq V]
    (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (T : Finset (Option V)) :
    (abigMeasure J beta h).real
        (connEvent (withGhost G) (T : Set (Option V)) (some o) {none}) <=
      abigMag G J o beta h := by
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  exact abig_connEvent_mono_set (withGhost G) (Set.subset_univ _)
    (some o) none

omit [Countable V] in

theorem abig_finiteMag_mono [DecidableEq V]
    (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V) (beta h : Real)
    {S T : Finset (Option V)} (hST : S ⊆ T) :
    (abigMeasure J beta h).real
        (connEvent (withGhost G) (S : Set (Option V)) (some o) {none}) <=
      (abigMeasure J beta h).real
        (connEvent (withGhost G) (T : Set (Option V)) (some o) {none}) := by
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  exact abig_connEvent_mono_set (withGhost G) hST (some o) none


theorem abig_aizenmanBarskyPhysical_of_fieldRegular_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 : Real)
    (hJ0 : 0 <= J0) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hrow : forall n (x : S n),
      abcrIncidentCoupling (abigWindowGraph G (S n))
        (abigWindowCoupling J (S n)) x <= J0)
    (hInfiniteTarget : forall beta h, 0 <= beta -> 0 <= h ->
      forall n (x : S n),
        abigMag G J (x : V) beta h <= abigMag G J o beta h)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n))
    (hcontLimit : forall beta h, 0 <= beta -> 0 < h ->
      ContinuousAt (Function.uncurry (abigMag G J o)) (beta, h))
    (hfieldDiffLimit : forall beta h, 0 <= beta -> 0 < h ->
      DifferentiableAt Real (fun t => abigMag G J o beta t) h) :
    AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
  let Mn : Nat -> Real -> Real -> Real := fun n beta h =>
    abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
      ⟨o, ho n⟩ beta h
  let Cn : Nat -> Real -> Real -> Real := fun n beta h =>
    abigWindowEnvelope G J (S n) ⟨o, ho n⟩ beta h
  intro beta hbeta h hh
  have hmonoLimit := abigMag_monotoneOn_field_of_exhaustion
    G J o beta hbeta hJ hJsupport S ho hmonoWindow hcover
  have hfieldDiff := hfieldDiffLimit beta h hbeta hh
  have hfieldNN := abigMag_deriv_field_nonneg_of_monotone
    G J o beta h hh hmonoLimit hfieldDiff
  apply abtp_inequality_at_of_fieldDifferentiable_physical_envelope
    Mn Cn (abigMag G J o) J0 beta h hJ0 hbeta hh
    (abigMag_nonneg G J o beta h)
  · intro n b t hb ht
    simpa [Mn, Cn, mul_assoc] using
      (abig_window_aizenmanBarsky_finiteEnvelope
        G J (S n) ⟨o, ho n⟩ b t J0 hb ht hJ (hrow n))
  · intro n b t hb ht
    apply abfa_deriv_field_nonneg
      (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
        ⟨o, ho n⟩ b t
    · intro e he
      induction e using Sym2.inductionOn with
      | _ x y => simpa using hJ s((x : V), (y : V))
    · exact hb
    · exact ht
  · intro n t ht
    exact abigWindowEnvelope_monotoneOn_beta
      G J (S n) ⟨o, ho n⟩ t hJ ht
  · intro n b hb
    exact abigWindowEnvelope_monotoneOn_field
      G J (S n) ⟨o, ho n⟩ b hJ hb
  · intro n b t hb ht
    exact abigWindowEnvelope_le_mag G J (S n) ⟨o, ho n⟩ b t
      hb ht hJ hJsupport (hInfiniteTarget b t hb ht n)
  · intro b t hb ht
    exact abig_tendsto_abfaMag_exhaustion G J o b t hb ht hJ hJsupport
      S ho hmonoWindow hcover
  · exact hcontLimit beta h hbeta hh
  · intro n b t
    exact abfa_differentiableAt_mag_joint
      (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
        ⟨o, ho n⟩ b t
  · exact hfieldDiff
  · exact hfieldNN


theorem abig_aizenmanBarskyPhysical_unconditional_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 : Real)
    (hJ0 : 0 <= J0) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hrow : forall n (x : S n),
      abcrIncidentCoupling (abigWindowGraph G (S n))
        (abigWindowCoupling J (S n)) x <= J0)
    (hInfiniteTarget : forall beta h, 0 <= beta -> 0 <= h ->
      forall n (x : S n),
        abigMag G J (x : V) beta h <= abigMag G J o beta h)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n)) :
    AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
  apply abig_aizenmanBarskyPhysical_of_fieldRegular_exhaustion
    G J o J0 hJ0 hJ hJsupport S ho hrow hInfiniteTarget hmonoWindow hcover
  · intro beta h hbeta hh
    exact abigMag_continuousAt_joint_of_exhaustion
      G J o J0 beta h hJ0 hbeta hh hJ hJsupport S ho hrow
        hInfiniteTarget hmonoWindow hcover
  · intro beta h hbeta hh
    exact abigMag_differentiableAt_field_of_exhaustion
      G J o beta h hbeta hh hJ hJsupport S ho hmonoWindow hcover


theorem abig_aizenmanBarskyPhysical_of_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 : Real)
    (hJ0 : 0 <= J0) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hrow : forall n (x : S n),
      abcrIncidentCoupling (abigWindowGraph G (S n))
        (abigWindowCoupling J (S n)) x <= J0)
    (hInfiniteTarget : forall beta h, 0 <= beta -> 0 <= h ->
      forall n (x : S n),
        abigMag G J (x : V) beta h <= abigMag G J o beta h)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n))
    (hjointLimit : forall beta h, 0 <= beta -> 0 < h ->
      DifferentiableAt Real (Function.uncurry (abigMag G J o)) (beta, h)) :
    AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
  apply abig_aizenmanBarskyPhysical_of_fieldRegular_exhaustion
    G J o J0 hJ0 hJ hJsupport S ho hrow hInfiniteTarget hmonoWindow hcover
  · intro beta h hbeta hh
    exact (hjointLimit beta h hbeta hh).continuousAt
  · intro beta h hbeta hh
    have hjoint := hjointLimit beta h hbeta hh
    have hline : DifferentiableAt Real (fun t : Real => (beta, t)) h :=
      (differentiableAt_const beta).prodMk differentiableAt_id
    simpa [Function.comp_def, Function.uncurry] using hjoint.comp h hline


theorem abig_aizenmanBarskyPhysical_of_tsum_transitive_fieldRegular
    [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 : Real)
    (hJ0 : 0 <= J0) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (hsum : forall x, Summable (fun y =>
      if G.Adj x y then J s(x, y) else 0))
    (hrow : forall x, (∑' y,
      if G.Adj x y then J s(x, y) else 0) <= J0)
    (move : V -> (V ≃ V)) (hmove : forall x, move x o = x)
    (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
    (hJinv : forall x u v, J s(move x u, move x v) = J s(u, v))
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n))
    (hcontLimit : forall beta h, 0 <= beta -> 0 < h ->
      ContinuousAt (Function.uncurry (abigMag G J o)) (beta, h))
    (hfieldDiffLimit : forall beta h, 0 <= beta -> 0 < h ->
      DifferentiableAt Real (fun t => abigMag G J o beta t) h) :
    AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
  apply abig_aizenmanBarskyPhysical_of_fieldRegular_exhaustion
    G J o J0 hJ0 hJ hJsupport S ho
  · intro n x
    exact abigWindow_incidentCoupling_le G J J0
      (abigUniformFiniteRowBound_of_tsum G J J0 hJ hsum hrow) (S n) x
  · intro beta h hbeta hh n x
    exact le_of_eq (abigMag_eq_of_transitive G J o beta h move hmove
      hG hJinv (fun k => abigGhostWindow (S k)) hcover (x : V))
  · exact hmonoWindow
  · exact hcover
  · exact hcontLimit
  · exact hfieldDiffLimit


theorem abig_aizenmanBarskyPhysical_of_tsum_transitive_unconditional
    [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 : Real)
    (hJ0 : 0 <= J0) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (hsum : forall x, Summable (fun y =>
      if G.Adj x y then J s(x, y) else 0))
    (hrow : forall x, (∑' y,
      if G.Adj x y then J s(x, y) else 0) <= J0)
    (move : V -> (V ≃ V)) (hmove : forall x, move x o = x)
    (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
    (hJinv : forall x u v, J s(move x u, move x v) = J s(u, v))
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n)) :
    AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
  apply abig_aizenmanBarskyPhysical_unconditional_exhaustion
    G J o J0 hJ0 hJ hJsupport S ho
  · intro n x
    exact abigWindow_incidentCoupling_le G J J0
      (abigUniformFiniteRowBound_of_tsum G J J0 hJ hsum hrow) (S n) x
  · intro beta h hbeta hh n x
    exact le_of_eq (abigMag_eq_of_transitive G J o beta h move hmove
      hG hJinv (fun k => abigGhostWindow (S k)) hcover (x : V))
  · exact hmonoWindow
  · exact hcover


theorem abig_aizenmanBarskyPhysical_of_transitive_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 : Real)
    (hJ0 : 0 <= J0) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (hrow : abigUniformFiniteRowBound G J J0)
    (move : V -> (V ≃ V)) (hmove : forall x, move x o = x)
    (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
    (hJinv : forall x u v, J s(move x u, move x v) = J s(u, v))
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n))
    (hjointLimit : forall beta h, 0 <= beta -> 0 < h ->
      DifferentiableAt Real (Function.uncurry (abigMag G J o)) (beta, h)) :
    AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
  apply abig_aizenmanBarskyPhysical_of_exhaustion
    G J o J0 hJ0 hJ hJsupport S ho
  · intro n x
    exact abigWindow_incidentCoupling_le G J J0 hrow (S n) x
  · intro beta h hbeta hh n x
    exact le_of_eq (abigMag_eq_of_transitive G J o beta h move hmove
      hG hJinv (fun k => abigGhostWindow (S k)) hcover (x : V))
  · exact hmonoWindow
  · exact hcover
  · exact hjointLimit


theorem abig_aizenmanBarskyPhysical_of_tsum_transitive_exhaustion
    [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 : Real)
    (hJ0 : 0 <= J0) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (hsum : forall x, Summable (fun y =>
      if G.Adj x y then J s(x, y) else 0))
    (hrow : forall x, (∑' y,
      if G.Adj x y then J s(x, y) else 0) <= J0)
    (move : V -> (V ≃ V)) (hmove : forall x, move x o = x)
    (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
    (hJinv : forall x u v, J s(move x u, move x v) = J s(u, v))
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n))
    (hjointLimit : forall beta h, 0 <= beta -> 0 < h ->
      DifferentiableAt Real (Function.uncurry (abigMag G J o)) (beta, h)) :
    AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
  apply abig_aizenmanBarskyPhysical_of_transitive_exhaustion
    G J o J0 hJ0 hJ hJsupport
    (abigUniformFiniteRowBound_of_tsum G J J0 hJ hsum hrow)
    move hmove hG hJinv S ho hmonoWindow hcover hjointLimit


theorem abig_ghost_edge_prob (J : Sym2 V -> Real) (beta h : Real)
    (hh : 0 <= h) (x : V) :
    (abigMeasure J beta h).real
        {omega | omega s(some x, none) = true} = qField h := by
  rw [abig_coord_true_prob, abigParam_some_none]
  exact Real.coe_toNNReal _ (qField_mem h hh).1


theorem abig_physical_edge_prob (J : Sym2 V -> Real) (beta h : Real)
    (hbeta : 0 <= beta) {x y : V} (hJ : 0 <= J s(x, y)) :
    (abigMeasure J beta h).real
        {omega | omega s(some x, some y) = true} = pBeta (J s(x, y)) beta := by
  rw [abig_coord_true_prob, abigParam_some_some]
  exact Real.coe_toNNReal _ (pBeta_nonneg (mul_nonneg hbeta hJ))

end Marginals
end Sharpness
end StatMech
