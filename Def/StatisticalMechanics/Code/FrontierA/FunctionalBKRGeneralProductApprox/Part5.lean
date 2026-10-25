/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductFinite
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductApprox.Part5
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


universe w


noncomputable def finiteCoordinateFactorOn_piece
    [∀ e, Nonempty (S e)] (K : Set E) {A : Set (∀ e, S e)}
    (hAfin : IsFiniteCoordinateSet A) (hAdep : PiSetDependsOn K A)
    (c : ℝ) (hc : 0 ≤ c) :
    FiniteCoordinateFactorOn.{u, v, 0} K (A.indicator fun _ => c) := by
  classical
  let data := finiteCoordinateSetData hAfin
  let n := data.n
  let q := data.q
  let B := data.B
  have hq : ∀ e, Measurable (q e) := data.measurable_q
  have hAeq : A = (fun x e => q e (x e)) ⁻¹' B := data.eq_preimage
  let base : ∀ e, S e := fun e => Classical.choice inferInstance
  let decode : (∀ e, Fin (n e)) → (∀ e, S e) := fun y e =>
    finiteQuotientRepresentative q e (y e)
  let decodeK : (∀ e, Fin (n e)) → (∀ e, S e) := fun y e =>
    if he : e ∈ K then decode y e else base e
  let H : (∀ e, Fin (n e)) → ℝ := fun y =>
    if decodeK y ∈ A then c else 0
  refine
    { T := fun e => Fin (n e)
      fintype_T := fun _ => inferInstance
      measurableSpace_T := fun _ => inferInstance
      measurableSingleton_T := fun _ => inferInstance
      q := q
      measurable_q := hq
      H := H
      nonneg_H := fun y => by dsimp [H]; split <;> positivity
      dependsOn_H := ?_
      eq_comp := ?_ }
  · intro y z hyz
    have hdecode : decodeK y = decodeK z := by
      funext e
      by_cases he : e ∈ K
      · simp [decodeK, decode, he, hyz e he]
      · simp [decodeK, he]
    unfold H
    rw [hdecode]
  · funext x
    have hqdecode : (fun e => q e (decode (fun e => q e (x e)) e)) =
        (fun e => q e (x e)) := by
      funext e
      exact finiteQuotientRepresentative_rightInverse q e (x e)
    have hfull : decode (fun e => q e (x e)) ∈ A ↔ x ∈ A := by
      rw [hAeq]
      simp only [Set.mem_preimage]
      rw [hqdecode]
    have hagree : piAgreeOn K (decode (fun e => q e (x e)))
        (decodeK (fun e => q e (x e))) := by
      intro e he
      simp [decodeK, he]
    have hK : decodeK (fun e => q e (x e)) ∈ A ↔ x ∈ A :=
      (hAdep hagree).symm.trans hfull
    by_cases hx : x ∈ A
    · have hdecodeMem : decodeK (fun e => q e (x e)) ∈ A := hK.mpr hx
      simp [Set.indicator_apply, H, hx, hdecodeMem]
    · have hdecodeNotMem : decodeK (fun e => q e (x e)) ∉ A :=
        fun h => hx (hK.mp h)
      simp [Set.indicator_apply, H, hx, hdecodeNotMem]

universe z wF wG

noncomputable def finiteCoordinateFactorOn_sup'
    {I : Type z} [Fintype I] [DecidableEq I]
    (hI : (Finset.univ : Finset I).Nonempty) (K : Set E)
    (a : I → (∀ e, S e) → ℝ)
    (ha : ∀ i, FiniteCoordinateFactorOn.{u, v, w} K (a i)) :
    FiniteCoordinateFactorOn.{u, v, max w z} K
      (fun x => (Finset.univ : Finset I).sup' hI (fun i => a i x)) := by
  classical
  letI componentFintype : ∀ i e, Fintype ((ha i).T e) :=
    fun i e => (ha i).fintype_T e
  letI componentMeasurableSpace : ∀ i e, MeasurableSpace ((ha i).T e) :=
    fun i e => (ha i).measurableSpace_T e
  letI componentMeasurableSingleton :
      ∀ i e, MeasurableSingletonClass ((ha i).T e) :=
    fun i e => (ha i).measurableSingleton_T e
  let T : E → Type (max w z) := fun e => ∀ i, (ha i).T e
  let instF : ∀ e, Fintype (T e) := fun _ => inferInstance
  let instM : ∀ e, MeasurableSpace (T e) := fun _ => inferInstance
  let instS : ∀ e, MeasurableSingletonClass (T e) := fun _ => inferInstance
  let q : ∀ e, S e → T e := fun e x i => (ha i).q e x
  let H : (∀ e, T e) → ℝ := fun y =>
    (Finset.univ : Finset I).sup' hI fun i =>
      (ha i).H (fun e => y e i)
  refine
    { T := T
      fintype_T := instF
      measurableSpace_T := instM
      measurableSingleton_T := instS
      q := q
      measurable_q := ?_
      H := H
      nonneg_H := ?_
      dependsOn_H := ?_
      eq_comp := ?_ }
  · intro e
    apply measurable_pi_lambda
    intro i
    exact (ha i).measurable_q e
  · intro y
    unfold H
    let i := Classical.choose hI
    calc
      0 ≤ (ha i).H (fun e => y e i) := (ha i).nonneg_H _
      _ ≤ (Finset.univ : Finset I).sup' hI
          (fun j => (ha j).H (fun e => y e j)) :=
        Finset.le_sup' (fun j : I => (ha j).H (fun e => y e j))
          (Finset.mem_univ i)
  · intro y z hyz
    unfold H
    apply congrArg ((Finset.univ : Finset I).sup' hI)
    funext i
    apply (ha i).dependsOn_H
    intro e he
    exact congrFun (hyz e he) i
  · funext x
    unfold H q
    apply congrArg ((Finset.univ : Finset I).sup' hI)
    funext i
    exact congrFun (ha i).eq_comp x

end StatMech.FrontierA
