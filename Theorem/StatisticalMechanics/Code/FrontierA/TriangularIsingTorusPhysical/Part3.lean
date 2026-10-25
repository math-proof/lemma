/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusShiftedAssembly
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorSandwich.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical.Part2
open scoped BigOperators
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Onsager

theorem triangularTorusNormalizedSectorMaxSequence_eq
    (J1 J2 J3 : Real) (rho : Complex) (n : Nat) :
    triangularTorusNormalizedSectorMaxSequence J1 J2 J3 rho n =
      (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^
          ((n + 3) * (n + 3)) *
        arfSectorNormMax (triangularTorusSectorSequence
          (fun L => triangularTorusRealEdgeWeight L
            (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) n) := by
  let C : Real := (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^
    ((n + 3) * (n + 3))
  letI : Fact (2 < n + 3) := ⟨by omega⟩
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  unfold triangularTorusNormalizedSectorMaxSequence
    triangularTorusNormalizedSectorSequence triangularTorusSectorSequence
  change arfSectorNormMax (fun a b => (C : Complex) *
      triangularTorusWeightedSpinCharacterSum (n + 3)
        (triangularTorusEdgeWeight (n + 3)
          (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b) = _
  rw [← triangularTorusEdgeWeight_real_cast]
  exact arfSectorNormMax_nonneg_real_mul C hC _


theorem triangularTorusNormalizedEven_log_gap_tendsto_zero
    (J1 J2 J3 : Real) (rho : Complex)
    (hJ1 : 0 ≤ J1) (hJ2 : 0 ≤ J2) (hJ3 : 0 ≤ J3) :
    Filter.Tendsto
      (fun n : Nat =>
        (Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) -
          Real.log (triangularTorusNormalizedSectorMaxSequence
            J1 J2 J3 rho n)) / (n + 3 : Real) ^ 2)
      Filter.atTop (nhds 0) := by
  let weight : (L : Nat) → Sym2 (ZMod L × ZMod L) → Real :=
    fun L => triangularTorusRealEdgeWeight L
      (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)
  have htanh1 : 0 ≤ Real.tanh J1 := real_tanh_nonneg hJ1
  have htanh2 : 0 ≤ Real.tanh J2 := real_tanh_nonneg hJ2
  have htanh3 : 0 ≤ Real.tanh J3 := real_tanh_nonneg hJ3
  have hbase := triangularTorusEvenSubgraphSum_normalizedLog_gap_tendsto_zero
    weight (fun L => triangularTorusRealEdgeWeight_nonneg
      L htanh1 htanh2 htanh3)
  apply hbase.congr'
  filter_upwards [] with n
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  let C : Real := (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L)
  let E : Real := inhomogeneousEvenSubgraphSum (triangularTorusGraph L)
    (weight L)
  let M : Real := arfSectorNormMax (triangularTorusSectorSequence weight n)
  have hweight : ∀ edge, 0 ≤ weight L edge :=
    triangularTorusRealEdgeWeight_nonneg L htanh1 htanh2 htanh3
  have hE : 0 < E :=
    inhomogeneousEvenSubgraphSum_pos_of_nonneg
      (triangularTorusGraph L) (weight L) hweight
  have hM : 0 < M := by
    let sector : Fin 2 -> Fin 2 -> Complex :=
      triangularTorusSectorSequence weight n
    have hdom : forall a b, ‖sector a b‖ ≤ E := by
      intro a b
      dsimp only [sector, triangularTorusSectorSequence, E]
      exact triangularTorusWeightedSpin_norm_le_evenSubgraphSum
        L hweight a b
    have harf := two_mul_triangularTorusEvenSubgraphSum_eq_spin L (weight L)
    have harf' : ((2 * E : Real) : Complex) =
        sector 1 1 + sector 0 1 + sector 1 0 - sector 0 0 := by
      dsimp only [sector, E]
      simpa only [Nat.cast_ofNat, Complex.ofReal_mul] using harf
    have hbound := arfSectorNormMax_le_and_le_two_mul E sector hE hdom harf'
    dsimp only [M]
    nlinarith [hbound.2]
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hmax := triangularTorusNormalizedSectorMaxSequence_eq
    J1 J2 J3 rho n
  simp only [triangularTorusNormalizedEvenSequence,
    triangularTorusEvenSubgraphSequence]
  change (Real.log E - Real.log M) / (n + 3 : Real) ^ 2 =
    (Real.log (C * E) -
      Real.log (triangularTorusNormalizedSectorMaxSequence
        J1 J2 J3 rho n)) / (n + 3 : Real) ^ 2
  rw [hmax]
  rw [Real.log_mul hC.ne' hE.ne', Real.log_mul hC.ne' hM.ne']
  ring


theorem triangularTorusNormalizedEven_logDensity_tendsto
    (J1 J2 J3 : Real) (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hJ1 : 0 ≤ J1) (hJ2 : 0 ≤ J2) (hJ3 : 0 ≤ J3)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Filter.Tendsto
      (fun n : Nat =>
        Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) /
          (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds ((1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi,
          ∫ k2 in (-Real.pi)..Real.pi,
            Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
  have hgap := triangularTorusNormalizedEven_log_gap_tendsto_zero
    J1 J2 J3 rho hJ1 hJ2 hJ3
  have hmax := triangularTorusNormalizedSectorMax_logDensity_tendsto
    J1 J2 J3 rho hrho hpos
  have hadd := hgap.add hmax
  have hadd' : Filter.Tendsto
      (fun n : Nat =>
        (Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) -
            Real.log (triangularTorusNormalizedSectorMaxSequence
              J1 J2 J3 rho n)) / (n + 3 : Real) ^ 2 +
          Real.log (triangularTorusNormalizedSectorMaxSequence
            J1 J2 J3 rho n) / (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds ((1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi,
          ∫ k2 in (-Real.pi)..Real.pi,
            Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
    simpa only [zero_add] using hadd
  apply hadd'.congr'
  filter_upwards [] with n
  ring

theorem prod_triangularPositiveEdgeSources
    {A : Type*} [CommMonoid A]
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ⊆ (triangularTorusGraph L).edgeFinset)
    (f : Sym2 (ZMod L × ZMod L) → A) :
    (∏ edge ∈ F, f edge) =
      ∏ a : Fin 3, ∏ p ∈ triangularPositiveEdgeSources L F a,
        f (triangularPositiveEdge L a p) := by
  simpa only using
    (sum_triangularPositiveEdgeSources (A := Additive A) L F hF
      (fun edge => Additive.ofMul (f edge)))

theorem triangularPositiveEdgeSources_edgeFinset
    (L : Nat) [Fact (2 < L)] (a : Fin 3) :
    triangularPositiveEdgeSources L (triangularTorusGraph L).edgeFinset a =
      Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro p
  rw [triangularPositiveEdgeSources, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [SimpleGraph.mem_edgeFinset]
  unfold triangularPositiveEdge
  exact (triangularTorusDartEquiv L
    (p, triangularTorusPositiveDirection a)).adj

theorem triangularTorusRealEdgeWeight_positiveEdge
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (a : Fin 3) (p : ZMod L × ZMod L) :
    triangularTorusRealEdgeWeight L J1 J2 J3
        (triangularPositiveEdge L a p) =
      ![J1, J2, J3] a := by
  apply Complex.ofReal_injective
  rw [triangularTorusRealEdgeWeight_cast]
  unfold triangularPositiveEdge
  rw [triangularTorusEdgeWeight_dart]
  fin_cases a <;>
    simp [triangularTorusPositiveDirection,
      triangularTorusDirectionWeight]

theorem prod_cosh_triangularTorusRealEdgeWeight
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real) :
    (∏ edge ∈ (triangularTorusGraph L).edgeFinset,
      Real.cosh (triangularTorusRealEdgeWeight L J1 J2 J3 edge)) =
      (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) := by
  rw [prod_triangularPositiveEdgeSources L
    (triangularTorusGraph L).edgeFinset (fun _ h => h) (fun edge =>
      Real.cosh (triangularTorusRealEdgeWeight L J1 J2 J3 edge))]
  simp_rw [triangularPositiveEdgeSources_edgeFinset,
    triangularTorusRealEdgeWeight_positiveEdge]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    ZMod.card]
  rw [show (∏ x : Fin 3, Real.cosh (![J1, J2, J3] x) ^ (L * L)) =
      Real.cosh J1 ^ (L * L) *
        (Real.cosh J2 ^ (L * L) * Real.cosh J3 ^ (L * L)) by
      simp]
  rw [mul_pow, mul_pow]
  ring

end StatMech.FrontierA
