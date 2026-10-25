/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
import Mathlib.Data.Finset.Sort
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part5
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwPortAngleRoot_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (p : KWDartPort G) :
    kwPortAngleRoot embedding p ≠ 0 :=
  Complex.exp_ne_zero _


theorem KWStraightLineEmbedding.turnPhase_eq_portRoots_of_rank_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d e : G.Dart)
    (hde : d.snd = e.fst)
    (hrank : kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G d.symm) <
      kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G e)) :
    embedding.turnPhase d e =
      -Complex.I * (kwPortAngleRoot embedding (kwPortOfDart G d.symm))⁻¹ *
        kwPortAngleRoot embedding (kwPortOfDart G e) := by
  let p := kwPortOfDart G d.symm
  let q := kwPortOfDart G e
  have hpfirst : p.1 = d.snd := by
    have h := kwDartOfPort_fst G p
    simpa [p] using h.symm
  have hqfirst : q.1 = e.fst := by
    have h := kwDartOfPort_fst G q
    simpa [q] using h.symm
  have hreal : (embedding.dartAngle (kwDartOfPort G p)).toReal <
      (embedding.dartAngle (kwDartOfPort G q)).toReal := by
    apply (kwAngularPortOrder_rank_lt_iff_angle_lt embedding
      (hpfirst.trans (hde.trans hqfirst.symm))).1
    exact hrank
  have hdangle : embedding.dartAngle d =
      embedding.dartAngle (kwDartOfPort G p) + (Real.pi : Real.Angle) := by
    simpa [p] using embedding.dartAngle_symm d.symm
  rw [← embedding.principalPhase_eq_turnPhase d e]
  unfold kwPrincipalHalfAnglePhase kwPortAngleRoot
  rw [hdangle, show embedding.dartAngle e =
      embedding.dartAngle (kwDartOfPort G q) by simp [q],
    kw_oppositeTurn_toReal_of_lt _ _ hreal]
  have hcalc :
      (((((embedding.dartAngle (kwDartOfPort G q)).toReal -
        (embedding.dartAngle (kwDartOfPort G p)).toReal - Real.pi : ℝ) : ℂ) *
          Complex.I) / 2) =
      (-(Real.pi : ℂ) / 2 * Complex.I) +
        (-((((embedding.dartAngle (kwDartOfPort G p)).toReal : ℂ) *
          Complex.I) / 2)) +
        (((embedding.dartAngle (kwDartOfPort G q)).toReal : ℂ) *
          Complex.I) / 2 := by
    push_cast
    ring
  rw [hcalc]
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_neg,
    Complex.exp_neg_pi_div_two_mul_I]


theorem KWStraightLineEmbedding.turnPhase_eq_portRoots_of_rank_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d e : G.Dart)
    (hde : d.snd = e.fst)
    (hrank : kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G e) <
      kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G d.symm)) :
    embedding.turnPhase d e =
      Complex.I * (kwPortAngleRoot embedding (kwPortOfDart G d.symm))⁻¹ *
        kwPortAngleRoot embedding (kwPortOfDart G e) := by
  let p := kwPortOfDart G d.symm
  let q := kwPortOfDart G e
  have hpfirst : p.1 = d.snd := by
    have h := kwDartOfPort_fst G p
    simpa [p] using h.symm
  have hqfirst : q.1 = e.fst := by
    have h := kwDartOfPort_fst G q
    simpa [q] using h.symm
  have hreal : (embedding.dartAngle (kwDartOfPort G q)).toReal <
      (embedding.dartAngle (kwDartOfPort G p)).toReal := by
    apply (kwAngularPortOrder_rank_lt_iff_angle_lt embedding
      (hqfirst.trans (hde.symm.trans hpfirst.symm))).1
    exact hrank
  have hdangle : embedding.dartAngle d =
      embedding.dartAngle (kwDartOfPort G p) + (Real.pi : Real.Angle) := by
    simpa [p] using embedding.dartAngle_symm d.symm
  rw [← embedding.principalPhase_eq_turnPhase d e]
  unfold kwPrincipalHalfAnglePhase kwPortAngleRoot
  rw [hdangle, show embedding.dartAngle e =
      embedding.dartAngle (kwDartOfPort G q) by simp [q],
    kw_oppositeTurn_toReal_of_gt _ _ hreal]
  have hcalc :
      (((((embedding.dartAngle (kwDartOfPort G q)).toReal -
        (embedding.dartAngle (kwDartOfPort G p)).toReal + Real.pi : ℝ) : ℂ) *
          Complex.I) / 2) =
      (((Real.pi : ℂ) / 2) * Complex.I) +
        (-((((embedding.dartAngle (kwDartOfPort G p)).toReal : ℂ) *
          Complex.I) / 2)) +
        (((embedding.dartAngle (kwDartOfPort G q)).toReal : ℂ) *
          Complex.I) / 2 := by
    push_cast
    ring
  rw [hcalc]
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_neg,
    Complex.exp_pi_div_two_mul_I]


end StatMech.FrontierA
