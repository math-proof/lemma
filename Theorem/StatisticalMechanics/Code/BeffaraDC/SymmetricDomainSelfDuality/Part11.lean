/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part10
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part15
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

theorem card_config_eq_four_mul_twoCoordinateRemainder
    {E : Type*} [Fintype E] [DecidableEq E] (a b : E) (hab : a ≠ b) :
    Fintype.card (E → Bool) =
      4 * Fintype.card (TwoCoordinateRemainder a b hab → Bool) := by
  calc
    Fintype.card (E → Bool) =
        Fintype.card
          (Bool × (Bool × (TwoCoordinateRemainder a b hab → Bool))) :=
      Fintype.card_congr (twoCoordinateSplit a b hab)
    _ = 4 * Fintype.card (TwoCoordinateRemainder a b hab → Bool) := by
      simp only [Fintype.card_prod, Fintype.card_bool]
      omega


theorem card_not_twoCoordinateTrue_eq_three_mul_card_twoCoordinateTrue
    {E : Type*} [Fintype E] [DecidableEq E] (a b : E) (hab : a ≠ b) :
    Fintype.card
        {omega : E → Bool // ¬(omega a = true ∧ omega b = true)} =
      3 * Fintype.card
        {omega : E → Bool // omega a = true ∧ omega b = true} := by
  classical
  let C := Fintype.card (TwoCoordinateRemainder a b hab → Bool)
  have htrue :
      Fintype.card
          {omega : E → Bool // omega a = true ∧ omega b = true} = C :=
    Fintype.card_congr (twoCoordinateTrueEquiv a b hab)
  have htotal : Fintype.card (E → Bool) = 4 * C :=
    card_config_eq_four_mul_twoCoordinateRemainder a b hab
  rw [Fintype.card_subtype_compl]
  rw [htrue, htotal]
  omega


theorem card_not_twoCoordinateTrue_ne_card_twoCoordinateTrue
    {E : Type*} [Fintype E] [DecidableEq E] (a b : E) (hab : a ≠ b) :
    Fintype.card
        {omega : E → Bool // ¬(omega a = true ∧ omega b = true)} ≠
      Fintype.card
        {omega : E → Bool // omega a = true ∧ omega b = true} := by
  classical
  have hratio :=
    card_not_twoCoordinateTrue_eq_three_mul_card_twoCoordinateTrue a b hab
  have hpos :
      0 < Fintype.card
        {omega : E → Bool // omega a = true ∧ omega b = true} := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨fun _ => true, by simp⟩⟩
  omega


theorem connectedVDomain_card_disconnected_eq_three_mul_connected :
    Fintype.card
        {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
          ¬connectedVDomain.MixedConnected omega} =
      3 * Fintype.card
        {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
          connectedVDomain.MixedConnected omega} := by
  classical
  let eConnected :
      {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
          connectedVDomain.MixedConnected omega} ≃
        {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
          omega connectedVLeftEdge = true ∧
            omega connectedVRightEdge = true} :=
    Equiv.subtypeEquivRight connectedVDomain_mixedConnected_iff
  let eDisconnected :
      {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
          ¬connectedVDomain.MixedConnected omega} ≃
        {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
          ¬(omega connectedVLeftEdge = true ∧
            omega connectedVRightEdge = true)} :=
    Equiv.subtypeEquivRight fun omega =>
      not_congr (connectedVDomain_mixedConnected_iff omega)
  calc
    Fintype.card
        {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
          ¬connectedVDomain.MixedConnected omega} =
        Fintype.card
          {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
            ¬(omega connectedVLeftEdge = true ∧
              omega connectedVRightEdge = true)} :=
      Fintype.card_congr eDisconnected
    _ = 3 * Fintype.card
          {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
            omega connectedVLeftEdge = true ∧
              omega connectedVRightEdge = true} :=
      card_not_twoCoordinateTrue_eq_three_mul_card_twoCoordinateTrue
        connectedVLeftEdge connectedVRightEdge connectedV_edges_ne
    _ = 3 * Fintype.card
          {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
            connectedVDomain.MixedConnected omega} := by
      exact congrArg (3 * ·) (Fintype.card_congr eConnected).symm


theorem connectedVDomain_no_mixedDualComplementRN (q : Real) :
    MixedDualComplementRN connectedVDomain q → False := by
  classical
  intro R
  have hratio := connectedVDomain_card_disconnected_eq_three_mul_connected
  have hequal := R.card_disconnected_eq_card_connected
  have hpos :
      0 < Fintype.card
        {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
          connectedVDomain.MixedConnected omega} := by
    apply Fintype.card_pos_iff.mpr
    refine ⟨⟨fun _ => true, ?_⟩⟩
    rw [connectedVDomain_mixedConnected_iff]
    simp
  omega


theorem mixedDisconnectionProbability_eq_dualPull
    (D : SymmetricDomain) (q : Real) (R : MixedDualComplementRN D q) :
    D.mixedDisconnectionProbability q =
      ∑ eta : ConfigSpace (Sym2 D.Vertex),
        if D.MixedConnected eta then D.mixedMass q (R.dual.symm eta) else 0 := by
  have hsum := Equiv.sum_comp R.dual
    (fun eta : ConfigSpace (Sym2 D.Vertex) =>
      if D.MixedConnected eta then D.mixedMass q (R.dual.symm eta) else 0)
  simpa [mixedDisconnectionProbability, R.connected_dual_iff] using hsum


theorem mixedDisconnectionProbability_le_q_sq_mul
    (D : SymmetricDomain) (q : Real) (R : MixedDualComplementRN D q) :
    D.mixedDisconnectionProbability q ≤
      q ^ 2 * D.mixedConnectionProbability q := by
  rw [mixedDisconnectionProbability_eq_dualPull D q R,
    mixedConnectionProbability, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro eta _
  by_cases hconn : D.MixedConnected eta
  · simp only [hconn, if_true]
    exact R.rn_upper eta
  · simp [hconn]


theorem mixedConnectionProbability_ge_one_div_one_add_q_sq
    (D : SymmetricDomain) {q : Real} (hq : 1 ≤ q)
    (R : MixedDualComplementRN D q) :
    1 / (1 + q ^ 2) ≤ D.mixedConnectionProbability q :=
  dlt_self_duality_estimate
    (mixedConnection_add_disconnection_eq_one D hq)
    (mixedDisconnectionProbability_le_q_sq_mul D q R)


theorem openConnectionProbability_ge_one_div_one_add_q_sq
    (D : SymmetricDomain) {q : Real} (hq : 1 ≤ q)
    (R : MixedDualComplementRN D q) :
    1 / (1 + q ^ 2) ≤ D.openConnectionProbability q := by
  rw [← mixedConnectionProbability_eq_openConnectionProbability D q]
  exact mixedConnectionProbability_ge_one_div_one_add_q_sq D hq R


end SymmetricDomain
end
end BeffaraDC
end StatMech
