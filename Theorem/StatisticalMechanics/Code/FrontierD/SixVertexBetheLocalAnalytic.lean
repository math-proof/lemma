/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticContinuation.Part2
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Algebra.Module.LocallyConvex
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem analyticAt_real_arctan (x : Real) :
    AnalyticAt Real Real.arctan x := by
  let a := Real.arctan x
  have hcos : Real.cos a ≠ 0 := (Real.cos_arctan_pos x).ne'
  have htan : AnalyticAt Real Real.tan a := by
    rw [show Real.tan = fun z => Real.sin z / Real.cos z by
      funext z
      rw [Real.tan_eq_sin_div_cos]]
    exact Real.analyticAt_sin.div Real.analyticAt_cos hcos
  let d : Real := 1 / Real.cos a ^ 2
  have hd : d ≠ 0 := by
    dsimp [d]
    positivity
  let i : Real ≃L[Real] Real :=
    ContinuousLinearEquiv.unitsEquivAut Real (.mk0 d hd)
  have hfderiv : fderiv Real Real.tan a = (i : Real →L[Real] Real) := by
    apply ContinuousLinearMap.ext
    intro y
    rw [(Real.hasDerivAt_tan hcos).hasFDerivAt.fderiv]
    simp [i, d, ContinuousLinearEquiv.unitsEquivAut_apply]
  dsimp [a] at htan hfderiv ⊢
  apply Real.tanPartialHomeomorph.analyticAt_symm
  · exact Set.mem_univ x
  · exact htan
  · exact hfderiv


theorem analyticAt_sixVertexTheta_joint
    (q : Real × (Real × Real)) (hc : 2 < q.1) :
    AnalyticAt Real
      (fun z : Real × (Real × Real) =>
        sixVertexTheta z.1 z.2.1 z.2.2) q := by
  unfold sixVertexTheta sixVertexThetaDenominator sixVertexDelta
  have hden : Real.cos q.2.1 + Real.cos q.2.2 -
      2 * ((2 - q.1 ^ 2) / 2) ≠ 0 := by
    have hx := Real.neg_one_le_cos q.2.1
    have hy := Real.neg_one_le_cos q.2.2
    nlinarith
  have hcA : AnalyticAt Real
      (fun z : Real × (Real × Real) => z.1) q :=
    (ContinuousLinearMap.fst Real Real (Real × Real)).analyticAt q
  have hxA : AnalyticAt Real
      (fun z : Real × (Real × Real) => z.2.1) q :=
    ((ContinuousLinearMap.fst Real Real Real).comp
      (ContinuousLinearMap.snd Real Real (Real × Real))).analyticAt q
  have hyA : AnalyticAt Real
      (fun z : Real × (Real × Real) => z.2.2) q :=
    ((ContinuousLinearMap.snd Real Real Real).comp
      (ContinuousLinearMap.snd Real Real (Real × Real))).analyticAt q
  have hnum : AnalyticAt Real
      (fun z : Real × (Real × Real) =>
        Real.sin z.2.1 - Real.sin z.2.2) q :=
    (Real.analyticAt_sin.comp hxA).sub (Real.analyticAt_sin.comp hyA)
  have hdeltaA : AnalyticAt Real
      (fun z : Real × (Real × Real) => (2 - z.1 ^ 2) / 2) q :=
    (analyticAt_const.sub (hcA.pow 2)).div_const
  have hdenA : AnalyticAt Real
      (fun z : Real × (Real × Real) =>
        Real.cos z.2.1 + Real.cos z.2.2 -
          2 * ((2 - z.1 ^ 2) / 2)) q :=
    ((Real.analyticAt_cos.comp hxA).add
      (Real.analyticAt_cos.comp hyA)).sub
        (analyticAt_const.mul hdeltaA)
  have hratio := hnum.div hdenA hden
  have harctan : AnalyticAt Real
      (fun z : Real × (Real × Real) =>
        Real.arctan ((Real.sin z.2.1 - Real.sin z.2.2) /
          (Real.cos z.2.1 + Real.cos z.2.2 -
            2 * ((2 - z.1 ^ 2) / 2)))) q :=
    (analyticAt_real_arctan _).comp hratio
  exact (hyA.sub hxA).add (analyticAt_const.mul harctan)


theorem analyticAt_sixVertexBetheResidual_family
    (N n : Nat) (q : Real × (Fin n → Real)) (hc : 2 < q.1) :
    AnalyticAt Real
      (fun z : Real × (Fin n → Real) =>
        fun j => sixVertexBetheResidual z.1 N n z.2 j) q := by
  apply AnalyticAt.pi
  intro j
  let sndP : (Real × (Fin n → Real)) →L[Real] (Fin n → Real) :=
    ContinuousLinearMap.snd Real Real (Fin n → Real)
  have hcA : AnalyticAt Real
      (fun z : Real × (Fin n → Real) => z.1) q :=
    (ContinuousLinearMap.fst Real Real (Fin n → Real)).analyticAt q
  have hjA : AnalyticAt Real
      (fun z : Real × (Fin n → Real) => z.2 j) q :=
    ((ContinuousLinearMap.proj j).comp sndP).analyticAt q
  have htheta (k : Fin n) : AnalyticAt Real
      (fun z : Real × (Fin n → Real) =>
        sixVertexTheta z.1 (z.2 j) (z.2 k)) q := by
    have hkA : AnalyticAt Real
        (fun z : Real × (Fin n → Real) => z.2 k) q :=
      ((ContinuousLinearMap.proj k).comp sndP).analyticAt q
    have hmap : AnalyticAt Real
        (fun z : Real × (Fin n → Real) =>
          (z.1, (z.2 j, z.2 k))) q := hcA.prod (hjA.prod hkA)
    exact (analyticAt_sixVertexTheta_joint
      (q.1, (q.2 j, q.2 k)) hc).comp
        (f := fun z : Real × (Fin n → Real) =>
          (z.1, (z.2 j, z.2 k))) (x := q) hmap
  have hsum : AnalyticAt Real
      (fun z : Real × (Fin n → Real) =>
        ∑ k, sixVertexTheta z.1 (z.2 j) (z.2 k)) q :=
    Finset.analyticAt_fun_sum Finset.univ (fun k _ => htheta k)
  unfold sixVertexBetheResidual
  exact ((analyticAt_const.mul hjA).add hsum).sub analyticAt_const


end
end StatMech.FrontierD
