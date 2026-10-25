/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceReduction
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPrincipalAngleMultiaffine
import Def.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitSpinor.Part2


namespace StatMech.FrontierA

open SimpleGraph

open scoped BigOperators


theorem kwPortAngleRoot_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (p : KWDartPort G) :
    kwPortAngleRoot embedding p ^ 2 =
      Complex.exp ((((embedding.dartAngle (kwDartOfPort G p)).toReal : Real) :
        Complex) * Complex.I) := by
  unfold kwPortAngleRoot
  rw [pow_two, ← Complex.exp_add]
  congr 1
  ring

theorem kwPortAngleRoot_sq_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) :
    kwPortAngleRoot embedding (kwPortOfDart G d.symm) ^ 2 =
      -(kwPortAngleRoot embedding (kwPortOfDart G d) ^ 2) := by
  rw [kwPortAngleRoot_sq, kwPortAngleRoot_sq]
  simp only [kwDartOfPort_portOfDart]
  unfold KWStraightLineEmbedding.dartAngle
  rw [Complex.arg_coe_angle_toReal_eq_arg,
    Complex.arg_coe_angle_toReal_eq_arg]
  let z := embedding.vertex d.snd - embedding.vertex d.fst
  have hz : z ≠ 0 := by
    simpa only [z] using embedding.dartVector_ne_zero d
  have hsymm : embedding.vertex d.fst - embedding.vertex d.snd = -z := by
    dsimp only [z]
    ring
  change Complex.exp
      ((Complex.arg (embedding.vertex d.fst - embedding.vertex d.snd) :
        Complex) * Complex.I) =
    -Complex.exp ((Complex.arg z : Complex) * Complex.I)
  rw [hsymm]
  have hzNorm : (norm z : Complex) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  have hneg := Complex.norm_mul_exp_arg_mul_I (-z)
  have hpos := Complex.norm_mul_exp_arg_mul_I z
  rw [norm_neg] at hneg
  apply (mul_left_cancel₀ hzNorm)
  calc
    (norm z : Complex) *
          Complex.exp ((Complex.arg (-z) : Complex) * Complex.I) =
        -z := hneg
    _ = -((norm z : Complex) *
          Complex.exp ((Complex.arg z : Complex) * Complex.I)) := by rw [hpos]
    _ = (norm z : Complex) *
          (-Complex.exp ((Complex.arg z : Complex) * Complex.I)) := by ring

theorem kwPortAngleRoot_sq_of_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) {p q : KWDartPort G}
    (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm) :
    kwPortAngleRoot embedding q ^ 2 =
      -(kwPortAngleRoot embedding p ^ 2) := by
  have hq : q = kwPortOfDart G (kwDartOfPort G p).symm := by
    apply kwDartOfPort_injective G
    simpa using hmatching
  rw [hq, kwPortAngleRoot_sq_symm]
  simp


theorem kwAngularSplitSpinorDirection_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) :
    kwAngularSplitSpinorDirection embedding d.symm =
      -kwAngularSplitSpinorDirection embedding d := by
  classical
  have hmatchingRev :
      kwDartOfPort G d.symm.snd =
          (kwDartOfPort G d.symm.fst).symm ↔
        kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm := by
    change kwDartOfPort G d.fst = (kwDartOfPort G d.snd).symm ↔
      kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      rw [h]
      simp
  by_cases hmatching :
      kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
  · have hmatching' :
        kwDartOfPort G d.symm.snd =
          (kwDartOfPort G d.symm.fst).symm := hmatchingRev.mpr hmatching
    unfold kwAngularSplitSpinorDirection
    rw [if_pos hmatching', if_pos hmatching]
    change kwPortAngleRoot embedding d.snd ^ 2 =
      -(kwPortAngleRoot embedding d.fst ^ 2)
    exact kwPortAngleRoot_sq_of_matching embedding hmatching
  · have hmatching' :
        ¬kwDartOfPort G d.symm.snd =
          (kwDartOfPort G d.symm.fst).symm := by
        simpa only [hmatchingRev] using hmatching
    have hadj := d.adj
    rw [kwOrderedDartPortSplitGraph_adj] at hadj
    have hinternal := hadj.resolve_left hmatching
    have hmatchingSwap :
        ¬kwDartOfPort G d.fst = (kwDartOfPort G d.snd).symm := by
      intro h
      apply hmatching
      rw [h]
      simp
    rcases hinternal.2 with hinc | hdec
    · have hlt : kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.snd := by omega
      have hnrev : ¬kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by omega
      unfold kwAngularSplitSpinorDirection
      change (if kwDartOfPort G d.fst = (kwDartOfPort G d.snd).symm then _
          else if kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.fst then -1 else 1) =
        -(if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then _
          else if kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.snd then -1 else 1)
      rw [if_neg hmatchingSwap, if_neg hmatching,
        if_neg hnrev, if_pos hlt]
      norm_num
    · have hnlt : ¬kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.snd := by omega
      have hrev : kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by omega
      unfold kwAngularSplitSpinorDirection
      change (if kwDartOfPort G d.fst = (kwDartOfPort G d.snd).symm then _
          else if kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.fst then -1 else 1) =
        -(if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then _
          else if kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.snd then -1 else 1)
      rw [if_neg hmatchingSwap, if_neg hmatching,
        if_pos hrev, if_neg hnlt]


end StatMech.FrontierA
