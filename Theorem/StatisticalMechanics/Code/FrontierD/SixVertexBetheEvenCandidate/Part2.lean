/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenCandidate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenCandidate
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedEvenChargeBetheRoots_symmetric
    {c : Real} (hc : 2 < c) (s k : Nat) :
    SixVertexRootSymmetric (sixVertexFixedEvenChargeBetheRoots hc s k) := by
  intro i
  have hsymm := (sixVertexFixedChargeBetheRoots_mem_open hc (2 * s) k).2.1
    (Fin.cast (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm i)
  have hind :
      Fin.cast (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm i.rev =
        (Fin.cast (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm i).rev := by
    apply Fin.ext
    simp [Fin.rev]
    omega
  unfold sixVertexFixedEvenChargeBetheRoots
  rw [hind, hsymm]

theorem prod_sixVertexFixedEvenChargeBetheRoots
    {c : Real} (hc : 2 < c) (s k : Nat) (f : Real -> Complex) :
    (∏ i, f (sixVertexFixedChargeBetheRoots hc (2 * s) k i)) =
      (∏ j, f (sixVertexFixedEvenPositiveBetheRoots hc s k j)) *
        ∏ j, f (-sixVertexFixedEvenPositiveBetheRoots hc s k j) := by
  let m := s + k + 1
  let p := sixVertexFixedEvenChargeBetheRoots hc s k
  let q := sixVertexFixedEvenPositiveBetheRoots hc s k
  have hreindex :
      (∏ i, f (sixVertexFixedChargeBetheRoots hc (2 * s) k i)) =
        ∏ i, f (p i) := by
    let e : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) ≃
        Fin (m + m) := (Fin.castOrderIso
          (sixVertexFixedEvenChargeBetheParticleCount_eq s k)).toEquiv
    apply Fintype.prod_equiv e
    intro i
    congr 2
  have hsymm := sixVertexFixedEvenChargeBetheRoots_symmetric hc s k
  have hfirst : (∏ i : Fin m, f (p (Fin.castAdd m i))) =
      ∏ i : Fin m, f (-q i) := by
    calc
      (∏ i : Fin m, f (p (Fin.castAdd m i))) =
          ∏ i : Fin m, f (-q i.rev) := by
        apply Finset.prod_congr rfl
        intro i _
        have hi := hsymm (Fin.castAdd m i).rev
        rw [Fin.rev_rev] at hi
        change p (Fin.castAdd m i) = -p (Fin.castAdd m i).rev at hi
        rw [hi]
        congr 2
        simp [q, sixVertexFixedEvenPositiveBetheRoots, p,
          sixVertexFixedEvenChargeBetheRoots, m, Fin.rev_castAdd]
      _ = ∏ i : Fin m, f (-q i) := by
        simpa using (Equiv.prod_comp Fin.revPerm (fun i => f (-q i)))
  rw [hreindex]
  change (∏ i, f (p i)) = _
  rw [Fin.prod_univ_add, hfirst]
  change (∏ i, f (-q i)) * (∏ i, f (q i)) =
    (∏ i, f (q i)) * ∏ i, f (-q i)
  rw [mul_comm]

theorem sixVertexFixedEvenChargeBetheEigenvalueCandidate_eq_symmetric
    {c : Real} (hc : 2 < c) (s k : Nat) :
    sixVertexBetheEigenvalueCandidate c
        (sixVertexFixedChargeBetheRoots hc (2 * s) k) =
      sixVertexSymmetricBetheEigenvalueCandidate c
        (sixVertexFixedEvenPositiveBetheRoots hc s k) := by
  unfold sixVertexBetheEigenvalueCandidate
    sixVertexSymmetricBetheEigenvalueCandidate
  rw [prod_sixVertexFixedEvenChargeBetheRoots hc s k
      (fun r => sixVertexBetheL c (sixVertexBethePhase r)),
    prod_sixVertexFixedEvenChargeBetheRoots hc s k
      (fun r => sixVertexBetheM c (sixVertexBethePhase r)),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]

end
end StatMech.FrontierD
