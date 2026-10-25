/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part14
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexForward_orientedSum_eq_nonnegativeTuples
    {N n : Nat} (c : Real) (p : Fin (n + 1) -> Real)
    (x : SixVertexSector N (n + 1)) :
    (∑ y ∈ (Finset.univ : Finset (SixVertexSector N (n + 1))).filter
        (fun y => SixVertexForwardInterlaced
          (sixVertexSectorRow y) (sixVertexSectorRow x)),
      (c : Complex) ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y) *
        sixVertexCoordinateBetheWave c p y) =
      ∑ q ∈ sixVertexBetheNonnegativeTuples N
          (sixVertexSectorIntCoordinates x),
        sixVertexBetheTupleWaveWeight N c p
          (sixVertexSectorIntCoordinates x) q := by
  classical
  apply Finset.sum_bij (fun y _ => sixVertexSectorIntCoordinates y)
  · intro y hy
    have hyx := (Finset.mem_filter.mp hy).2
    rw [mem_sixVertexBetheNonnegativeTuples]
    exact ⟨sixVertexForwardTuple_mem x y hyx,
      sixVertexForwardTuple_collisionFree x y hyx,
      by simp [sixVertexSectorIntCoordinates]⟩
  · intro y₁ hy₁ y₂ hy₂ heq
    apply (Set.powersetCard.ofFinEmbEquiv
      (n := n + 1) (I := Fin N)).symm.injective
    change sixVertexSectorPosition y₁ = sixVertexSectorPosition y₂
    ext i
    have hi := congrFun heq i
    unfold sixVertexSectorIntCoordinates at hi
    exact_mod_cast hi
  · intro q hq
    have hparts := (mem_sixVertexBetheNonnegativeTuples N _ q).mp hq
    let y := sixVertexBetheDirectTupleSector x q hparts.1 hparts.2.1 hparts.2.2
    have hyx := sixVertexBetheDirectTupleSector_forward x q
      hparts.1 hparts.2.1 hparts.2.2
    refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyx⟩, ?_⟩
    exact sixVertexSectorIntCoordinates_directTupleSector x q
      hparts.1 hparts.2.1 hparts.2.2
  · intro y hy
    have hyx := (Finset.mem_filter.mp hy).2
    unfold sixVertexBetheTupleWaveWeight sixVertexBetheTupleBoltzmann
    rw [sixVertexCoordinateBetheWave_eq_intWave,
      sixVertexForward_interior_card x y hyx,
      sixVertexSectorRowDistance_eq_two_mul_sdiff]
    have hcard : ((y : Finset (Fin N)) \ (x : Finset (Fin N))).card =
        ((x : Finset (Fin N)) \ (y : Finset (Fin N))).card := by
      rw [Finset.card_sdiff, Finset.card_sdiff, x.prop, y.prop,
        Finset.inter_comm]
    rw [hcard, pow_mul]

theorem SixVertexSatisfiesMultiplicativeBetheEquations.reverse_orientedSum_eq_negativeTuples
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) -> Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (x : SixVertexSector N (n + 1)) :
    (∑ y ∈ (Finset.univ : Finset (SixVertexSector N (n + 1))).filter
        (fun y => SixVertexForwardInterlaced
          (sixVertexSectorRow x) (sixVertexSectorRow y)),
      (c : Complex) ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y) *
        sixVertexCoordinateBetheWave c p y) =
      ∑ q ∈ sixVertexBetheNegativeTuples N
          (sixVertexSectorIntCoordinates x),
        sixVertexBetheTupleWaveWeight N c p
          (sixVertexSectorIntCoordinates x) q := by
  classical
  apply Finset.sum_bij (fun y _ =>
    sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y))
  · intro y hy
    have hxy := (Finset.mem_filter.mp hy).2
    rw [mem_sixVertexBetheNegativeTuples]
    exact ⟨sixVertexReverseTuple_mem x y hxy,
      sixVertexReverseTuple_collisionFree x y,
      sixVertexReverseTuple_first_neg y⟩
  · intro y₁ hy₁ y₂ hy₂ heq
    have heq' := congrArg (sixVertexBetheUnshiftCoordinates N) heq
    simp only [sixVertexBetheUnshiftCoordinates_shift] at heq'
    apply (Set.powersetCard.ofFinEmbEquiv
      (n := n + 1) (I := Fin N)).symm.injective
    change sixVertexSectorPosition y₁ = sixVertexSectorPosition y₂
    ext i
    have hi := congrFun heq' i
    unfold sixVertexSectorIntCoordinates at hi
    exact_mod_cast hi
  · intro q hq
    have hparts := (mem_sixVertexBetheNegativeTuples N _ q).mp hq
    let y := sixVertexBetheRotatedTupleSector x q
      hparts.1 hparts.2.1 hparts.2.2
    have hxy := sixVertexBetheRotatedTupleSector_forward x q
      hparts.1 hparts.2.1 hparts.2.2
    refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, ?_⟩
    have hcoord := sixVertexSectorIntCoordinates_rotatedTupleSector x q
      hparts.1 hparts.2.1 hparts.2.2
    rw [hcoord, sixVertexBetheShiftCoordinates_unshift]
  · intro y hy
    have hxy := (Finset.mem_filter.mp hy).2
    unfold sixVertexBetheTupleWaveWeight sixVertexBetheTupleBoltzmann
    rw [sixVertexCoordinateBetheWave_eq_intWave,
      sixVertexReverse_interior_card x y hxy,
      sixVertexSectorRowDistance_eq_two_mul_sdiff]
    have hcard : ((y : Finset (Fin N)) \ (x : Finset (Fin N))).card =
        ((x : Finset (Fin N)) \ (y : Finset (Fin N))).card := by
      rw [Finset.card_sdiff, Finset.card_sdiff, x.prop, y.prop,
        Finset.inter_comm]
    rw [hcard, pow_mul]
    rw [← hp.intWave_shift hc (sixVertexSectorIntCoordinates y)]

theorem sixVertexBetheCollisionFreeTuples_sum_split
    {n : Nat} (N : Nat) (x : Fin (n + 1) -> Int)
    (f : (Fin (n + 1) -> Int) -> Complex) :
    (∑ q ∈ sixVertexBetheCollisionFreeTuples N x, f q) =
      (∑ q ∈ sixVertexBetheNonnegativeTuples N x, f q) +
        ∑ q ∈ sixVertexBetheNegativeTuples N x, f q := by
  classical
  let A := sixVertexBetheNonnegativeTuples N x
  let B := sixVertexBetheNegativeTuples N x
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro q hA hB
    have hA' := (mem_sixVertexBetheNonnegativeTuples N x q).mp hA
    have hB' := (mem_sixVertexBetheNegativeTuples N x q).mp hB
    omega
  have hunion : A ∪ B = sixVertexBetheCollisionFreeTuples N x := by
    ext q
    simp only [Finset.mem_union]
    constructor
    · rintro (hA | hB)
      · have hp := (mem_sixVertexBetheNonnegativeTuples N x q).mp hA
        unfold sixVertexBetheCollisionFreeTuples
        exact Finset.mem_filter.mpr ⟨hp.1, hp.2.1⟩
      · have hp := (mem_sixVertexBetheNegativeTuples N x q).mp hB
        unfold sixVertexBetheCollisionFreeTuples
        exact Finset.mem_filter.mpr ⟨hp.1, hp.2.1⟩
    · intro hq
      have hbase := Finset.mem_filter.mp hq
      by_cases hq0 : 0 ≤ q 0
      · left
        rw [mem_sixVertexBetheNonnegativeTuples]
        exact ⟨hbase.1, hbase.2, hq0⟩
      · right
        rw [mem_sixVertexBetheNegativeTuples]
        exact ⟨hbase.1, hbase.2, lt_of_not_ge hq0⟩
  rw [← hunion, Finset.sum_union hdis]

theorem sixVertexBethe_sum_intervalTupleWeight
    {N n : Nat} (c : Real) (p : Fin (n + 1) -> Real)
    (x q : Fin (n + 1) -> Int) :
    (∑ sigma : Equiv.Perm (Fin (n + 1)),
      sixVertexBetheAmplitude c p sigma *
        sixVertexBetheIntervalTupleWeight N c
          (fun i => sixVertexBethePhase (p (sigma i))) x q) =
      sixVertexBetheTupleWaveWeight N c p x q := by
  rw [show (∑ sigma : Equiv.Perm (Fin (n + 1)),
      sixVertexBetheAmplitude c p sigma *
        sixVertexBetheIntervalTupleWeight N c
          (fun i => sixVertexBethePhase (p (sigma i))) x q) =
      sixVertexBetheTupleBoltzmann N c x q *
        ∑ sigma, sixVertexBetheAmplitude c p sigma *
          sixVertexBetheIntMonomial p sigma q by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sigma _
    rw [sixVertexBetheIntervalTupleWeight_eq_interior]
    unfold sixVertexBetheTupleBoltzmann sixVertexBetheIntMonomial
    ring]
  rfl

theorem SixVertexSatisfiesMultiplicativeBetheEquations.physicalCyclicIntervalExpansion
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) -> Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (x : SixVertexSector N (n + 1)) :
    (sixVertexSectorTransferComplex N (n + 1) c).mulVec
        (sixVertexCoordinateBetheWave c p) x =
      ∑ q ∈ sixVertexBetheCollisionFreeTuples N
          (sixVertexSectorIntCoordinates x),
        sixVertexBetheTupleWaveWeight N c p
          (sixVertexSectorIntCoordinates x) q := by
  rw [sixVertexSectorTransferComplex_mulVec_oriented,
    sixVertexForward_orientedSum_eq_nonnegativeTuples,
    hp.reverse_orientedSum_eq_negativeTuples hc,
    ← sixVertexBetheCollisionFreeTuples_sum_split]

theorem sixVertexBetheCollisionFreeIntervalSum_eq_tupleSum
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int) :
    sixVertexBetheCollisionFreeIntervalSum N c z x =
      ∑ q ∈ sixVertexBetheCollisionFreeTuples N x,
        sixVertexBetheIntervalTupleWeight N c z x q := by
  rfl


theorem sixVertexBetheShiftCoordinates_lt_sector {N n : Nat}
    (x : SixVertexSector N (n + 1)) (i : Fin (n + 1)) :
    sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates x) i <
      sixVertexSectorIntCoordinates x i := by
  induction i using Fin.cases with
  | zero =>
      simp only [sixVertexBetheShiftCoordinates, sixVertexSectorIntCoordinates,
        Fin.cases_zero]
      have hlast : (sixVertexSectorPosition x (Fin.last n)).val < N :=
        (sixVertexSectorPosition x (Fin.last n)).prop
      have hzero : 0 <= (sixVertexSectorPosition x 0).val := Nat.zero_le _
      omega
  | succ i =>
      simp only [sixVertexBetheShiftCoordinates, sixVertexSectorIntCoordinates,
        Fin.cases_succ]
      exact_mod_cast (sixVertexSectorPosition x).strictMono
        (Fin.castSucc_lt_succ (i := i))


theorem SixVertexSatisfiesMultiplicativeBetheEquations.physicalWordExpansion
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) -> Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
    SixVertexPhysicalWordExpansion (N := N) c p := by
  intro x
  rw [hp.physicalCyclicIntervalExpansion hc p x]
  let Q := sixVertexBetheCollisionFreeTuples N
    (sixVertexSectorIntCoordinates x)
  calc
    (∑ q ∈ Q, sixVertexBetheTupleWaveWeight N c p
        (sixVertexSectorIntCoordinates x) q) =
      ∑ q ∈ Q, ∑ sigma : Equiv.Perm (Fin (n + 1)),
        sixVertexBetheAmplitude c p sigma *
          sixVertexBetheIntervalTupleWeight N c
            (fun i => sixVertexBethePhase (p (sigma i)))
            (sixVertexSectorIntCoordinates x) q := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (sixVertexBethe_sum_intervalTupleWeight c p
        (sixVertexSectorIntCoordinates x) q).symm
    _ = ∑ sigma : Equiv.Perm (Fin (n + 1)),
        sixVertexBetheAmplitude c p sigma *
          sixVertexBetheCollisionFreeIntervalSum N c
            (fun i => sixVertexBethePhase (p (sigma i)))
            (sixVertexSectorIntCoordinates x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro sigma _
      rw [sixVertexBetheCollisionFreeIntervalSum_eq_tupleSum,
        Finset.mul_sum]
    _ = ∑ sigma : Equiv.Perm (Fin (n + 1)),
        sixVertexBetheAmplitude c p sigma *
          ∑ w : Finset (Fin (n + 1)),
            sixVertexBetheWordCoefficient c
              (fun i => sixVertexBethePhase (p (sigma i))) (Equiv.refl _) w *
            sixVertexBetheWordMonomial N
              (fun i => sixVertexBethePhase (p (sigma i))) (Equiv.refl _)
              (sixVertexSectorIntCoordinates x) w := by
      apply Finset.sum_congr rfl
      intro sigma _
      rw [sixVertexBetheCollisionFreeIntervalSum_eq_words]
      · exact fun i => sixVertexBetheShiftCoordinates_lt_sector x i
      · exact fun i => Complex.exp_ne_zero _
      · exact fun i => hphase (sigma i)
    _ = ∑ w : Finset (Fin (n + 1)),
        ∑ sigma, sixVertexBetheAmplitude c p sigma *
          sixVertexBetheWordCoefficient c
            (fun j => sixVertexBethePhase (p j)) sigma w *
          sixVertexBetheWordMonomial N
            (fun j => sixVertexBethePhase (p j)) sigma
            (sixVertexSectorIntCoordinates x) w := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro sigma _
      change sixVertexBetheAmplitude c p sigma *
          (sixVertexBetheWordCoefficient c
              (fun i => sixVertexBethePhase (p (sigma i))) (Equiv.refl _) w *
            sixVertexBetheWordMonomial N
              (fun i => sixVertexBethePhase (p (sigma i))) (Equiv.refl _)
              (sixVertexSectorIntCoordinates x) w) = _
      have hcoeff :
          sixVertexBetheWordCoefficient c
              (fun i => sixVertexBethePhase (p (sigma i))) (Equiv.refl _) w =
            sixVertexBetheWordCoefficient c
              (fun j => sixVertexBethePhase (p j)) sigma w := by
        unfold sixVertexBetheWordCoefficient
        apply Finset.prod_congr rfl
        intro i _
        simp [sixVertexBetheWordEdgeFactor]
      have hmono :
          sixVertexBetheWordMonomial N
              (fun i => sixVertexBethePhase (p (sigma i))) (Equiv.refl _)
              (sixVertexSectorIntCoordinates x) w =
            sixVertexBetheWordMonomial N
              (fun j => sixVertexBethePhase (p j)) sigma
              (sixVertexSectorIntCoordinates x) w := by
        unfold sixVertexBetheWordMonomial
        apply Finset.prod_congr rfl
        intro i _
        simp
      rw [hcoeff, hmono]
      ring


theorem SixVertexSatisfiesMultiplicativeBetheEquations.physicalCoordinateBetheEigenrelation
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) -> Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
    SixVertexCoordinateBetheEigenrelation (N := N) c p :=
  sixVertexCoordinateBetheEigenrelation_of_physicalWordExpansion
    hc p hp hphase (hp.physicalWordExpansion hc p hphase)

end
end StatMech.FrontierD
