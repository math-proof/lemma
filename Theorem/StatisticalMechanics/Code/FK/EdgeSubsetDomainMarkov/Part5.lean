/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.FK.EdgeSubsetDomainMarkov.Part7
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem edgeSubsetFibreCondEventMass_eq_activeBCProbOf
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hKH : K ≤ H) (psi : ConfigSpace (Sym2 V))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace K.edgeSet)) :
    edgeSubsetFibreCondEventMass K H B psi p q A =
      activeBCProbOf K (edgeSubsetInducedWiring K H B psi)
        (fun _ => p) q A := by
  classical
  unfold edgeSubsetFibreCondEventMass activeBCProbOf activeBCMean
  apply Finset.sum_congr rfl
  intro eta _
  rw [edgeSubsetFibre_condBcProb_eq_activeBCProb
    K H B hKH psi hp hp1 eta]


theorem edgeSubsetFibreCondEventMass_eq_bcEventMass
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hKH : K ≤ H) (psi : ConfigSpace (Sym2 V))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace K.edgeSet)) :
    edgeSubsetFibreCondEventMass K H B psi p q A =
      bcEventMass K (edgeSubsetInducedWiring K H B psi) p q
        (restrictActive K ⁻¹' A) := by
  classical
  rw [edgeSubsetFibreCondEventMass_eq_activeBCProbOf
      K H B hKH psi hp hp1 A,
    activeBCProbOf_eq_bcProb_preimage
      K (edgeSubsetInducedWiring K H B psi) hp hp1 hq]
  rfl

set_option maxHeartbeats 800000 in


theorem edgeSubsetFibreCondEventMass_eq_ambientSum
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (psi : ConfigSpace (Sym2 V)) (p q : Real)
    (A : Set (ConfigSpace K.edgeSet)) :
    edgeSubsetFibreCondEventMass K H B psi p q A =
      ∑ rho, (restrictActive K ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        condBcProb H B p q K.edgeFinset psi rho := by
  classical
  let S := condFibre K.edgeFinset psi
  let term := fun rho : ConfigSpace (Sym2 V) =>
    (restrictActive K ⁻¹' A).indicator (fun _ => (1 : Real)) rho *
      condBcProb H B p q K.edgeFinset psi rho
  have hrestrict : (∑ rho, term rho) = ∑ rho ∈ S, term rho := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro rho _ hrho
    have hnot : ¬AgreesOff K.edgeFinset psi rho := by
      rw [mem_condFibre] at hrho
      exact hrho
    unfold term condBcProb
    rw [if_neg hnot, mul_zero]
  symm
  calc
    (∑ rho, term rho) = ∑ rho ∈ S, term rho := hrestrict
    _ = ∑ rho : {rho // rho ∈ S}, term rho :=
      Finset.sum_subtype S (fun _ => Iff.rfl) term
    _ = ∑ eta, term ((edgeSubsetFibreEquiv K psi) eta) :=
      (Equiv.sum_comp (edgeSubsetFibreEquiv K psi)
        (fun rho => term rho.1)).symm
    _ = edgeSubsetFibreCondEventMass K H B psi p q A := by
      unfold edgeSubsetFibreCondEventMass term
      apply Finset.sum_congr rfl
      intro eta _
      change
        (restrictActive K ⁻¹' A).indicator (fun _ => (1 : Real))
            (edgeSubsetFibreConfig K psi eta) *
          condBcProb H B p q K.edgeFinset psi
            (edgeSubsetFibreConfig K psi eta) =
        A.indicator (fun _ => (1 : Real)) eta *
          condBcProb H B p q K.edgeFinset psi
            (edgeSubsetFibreConfig K psi eta)
      by_cases heta : eta ∈ A
      · rw [Set.indicator_of_mem heta,
          Set.indicator_of_mem (show
            edgeSubsetFibreConfig K psi eta ∈ restrictActive K ⁻¹' A by
              simpa using heta)]
      · rw [Set.indicator_of_notMem heta,
          Set.indicator_of_notMem (show
            edgeSubsetFibreConfig K psi eta ∉ restrictActive K ⁻¹' A by
              simpa using heta)]

end
end StatMech.FK
