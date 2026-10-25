/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks.Part6
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductCore.Part7
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


theorem HasBernoulliBlockRepresentation.equiv
    {T U : Type*} [Fintype T] [Fintype U]
    (e : T ≃ U) (w : U → ℝ)
    (h : HasBernoulliBlockRepresentation (fun t => w (e t))) :
    HasBernoulliBlockRepresentation w := by
  classical
  obtain ⟨n, phi, decode, hphi0, hphi1, hdecode, hexpect⟩ := h
  refine ⟨n, phi, e ∘ decode, hphi0, hphi1, e.surjective.comp hdecode, ?_⟩
  intro H
  rw [← e.sum_comp]
  simpa only [Function.comp_apply, Function.comp_def] using
    hexpect (H ∘ e)

theorem productExpectation_const {I : Type*} [Fintype I] [DecidableEq I]
    (phi : I → Bool → ℝ)
    (hphi1 : ∀ i, phi i false + phi i true = 1) (c : ℝ) :
    productExpectation phi (fun _ => c) = c := by
  classical
  unfold productExpectation
  rw [← Finset.sum_mul, sum_pweight_eq_one hphi1, one_mul]

theorem hasBernoulliBlockRepresentation_option
    {T : Type*} [Fintype T] [Nonempty T]
    (ih : ∀ (v : T → ℝ), (∀ t, 0 ≤ v t) → (∑ t, v t) = 1 →
      HasBernoulliBlockRepresentation v)
    (w : Option T → ℝ) (hw0 : ∀ t, 0 ≤ w t)
    (hw1 : (∑ t, w t) = 1) :
    HasBernoulliBlockRepresentation w := by
  classical
  let q : ℝ := w none
  let r : ℝ := ∑ t : T, w (some t)
  have hqr : q + r = 1 := by
    simpa only [q, r, Fintype.sum_option] using hw1
  have hr0 : 0 ≤ r := Finset.sum_nonneg fun t _ => hw0 (some t)
  have hq0 : 0 ≤ q := hw0 none
  by_cases hr : r = 0
  · let a : T := Classical.choice inferInstance
    let v : T → ℝ := fun t => if t = a then 1 else 0
    have hv0 : ∀ t, 0 ≤ v t := by
      intro t
      simp only [v]
      split <;> positivity
    have hv1 : (∑ t, v t) = 1 := by
      simp [v]
    obtain ⟨n, phi, decode, hphi0, hphi1, hdecode, hexpect⟩ := ih v hv0 hv1
    let psi : Fin (n + 1) → Bool → ℝ := fun i =>
      Fin.cases (fun b => if b then q else r) phi i
    let decode' : (Fin (n + 1) → Bool) → Option T := fun omega =>
      if omega 0 then none else some (decode (Fin.tail omega))
    refine ⟨n + 1, psi, decode', ?_, ?_, ?_, ?_⟩
    · intro i b
      refine Fin.cases ?_ (fun j => ?_) i
      · cases b <;> simp [psi, hr0, hq0]
      · simpa [psi] using hphi0 j b
    · intro i
      refine Fin.cases ?_ (fun j => hphi1 j) i
      simpa [psi, add_comm] using hqr
    · intro t
      cases t with
      | none =>
          refine ⟨Fin.cons true (fun _ => false), ?_⟩
          simp [decode']
      | some t =>
          obtain ⟨eta, heta⟩ := hdecode t
          refine ⟨Fin.cons false eta, ?_⟩
          simp [decode', heta]
    · intro H
      rw [productExpectation_fin_cons]
      rw [Fintype.sum_bool]
      simp only [psi, Fin.cases_zero, decode', Fin.cons_zero, Bool.false_eq_true,
        if_false, Bool.true_eq, if_true, Fin.tail_cons, Function.comp_apply]
      change q * productExpectation phi (fun _ => H none) +
          r * productExpectation phi ((fun t => H (some t)) ∘ decode) = _
      rw [productExpectation_const phi hphi1, hexpect]
      have hsome : ∀ t : T, w (some t) = 0 := by
        intro t
        have hle : w (some t) ≤ r := Finset.single_le_sum
          (fun u _ => hw0 (some u)) (Finset.mem_univ t)
        linarith [hw0 (some t)]
      rw [Fintype.sum_option]
      simp only [hsome, zero_mul, Finset.sum_const_zero, add_zero, hr, zero_mul]
      rfl
  · let v : T → ℝ := fun t => w (some t) / r
    have hv0 : ∀ t, 0 ≤ v t := fun t => div_nonneg (hw0 (some t)) hr0
    have hv1 : (∑ t, v t) = 1 := by
      simp only [v, ← Finset.sum_div, r]
      exact div_self hr
    obtain ⟨n, phi, decode, hphi0, hphi1, hdecode, hexpect⟩ := ih v hv0 hv1
    let psi : Fin (n + 1) → Bool → ℝ := fun i =>
      Fin.cases (fun b => if b then q else r) phi i
    let decode' : (Fin (n + 1) → Bool) → Option T := fun omega =>
      if omega 0 then none else some (decode (Fin.tail omega))
    refine ⟨n + 1, psi, decode', ?_, ?_, ?_, ?_⟩
    · intro i b
      refine Fin.cases ?_ (fun j => ?_) i
      · cases b <;> simp [psi, hr0, hq0]
      · simpa [psi] using hphi0 j b
    · intro i
      refine Fin.cases ?_ (fun j => hphi1 j) i
      simpa [psi, add_comm] using hqr
    · intro t
      cases t with
      | none =>
          refine ⟨Fin.cons true (fun _ => false), ?_⟩
          simp [decode']
      | some t =>
          obtain ⟨eta, heta⟩ := hdecode t
          refine ⟨Fin.cons false eta, ?_⟩
          simp [decode', heta]
    · intro H
      rw [productExpectation_fin_cons]
      rw [Fintype.sum_bool]
      simp only [psi, Fin.cases_zero, decode', Fin.cons_zero, Bool.false_eq_true,
        if_false, Bool.true_eq, if_true, Fin.tail_cons, Function.comp_apply]
      change q * productExpectation phi (fun _ => H none) +
          r * productExpectation phi ((fun t => H (some t)) ∘ decode) = _
      rw [productExpectation_const phi hphi1, hexpect]
      rw [Fintype.sum_option]
      simp only [v]
      calc
        q * H none + r * ∑ t, w (some t) / r * H (some t) =
            w none * H none + ∑ t, w (some t) * H (some t) := by
          rw [show q = w none from rfl]
          rw [Finset.mul_sum]
          apply congrArg (fun z => w none * H none + z)
          apply Finset.sum_congr rfl
          intro t _
          field_simp

theorem exists_bernoulliBlockRepresentation
    {T : Type u} [Fintype T] (w : T → ℝ)
    (hw0 : ∀ t, 0 ≤ w t) (hw1 : (∑ t, w t) = 1) :
    HasBernoulliBlockRepresentation w := by
  classical
  let P := fun (T : Type u) [Fintype T] =>
    ∀ (w : T → ℝ), (∀ t, 0 ≤ w t) → (∑ t, w t) = 1 →
      HasBernoulliBlockRepresentation w
  suffices h : P T by exact h w hw0 hw1
  refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ T
  · intro A B _ e hA w hw0 hw1
    letI : Fintype A := Fintype.ofEquiv B e.symm
    apply HasBernoulliBlockRepresentation.equiv e w
    apply hA (fun a => w (e a)) (fun a => hw0 (e a))
    simpa only [← e.sum_comp] using hw1
  · intro w _ hw1
    simp at hw1
  · intro A _ hA w hw0 hw1
    by_cases hne : Nonempty A
    · letI : Nonempty A := hne
      exact hasBernoulliBlockRepresentation_option hA w hw0 hw1
    · letI : IsEmpty A := not_nonempty_iff.mp hne
      let phi : Fin 0 → Bool → ℝ := fun i => Fin.elim0 i
      let decode : (Fin 0 → Bool) → Option A := fun _ => none
      refine ⟨0, phi, decode, ?_, ?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro t
        cases t with
        | none => exact ⟨fun i => Fin.elim0 i, rfl⟩
        | some a => exact isEmptyElim a
      · intro H
        change productExpectation phi (fun _ => H none) = _
        rw [productExpectation_const phi (fun i => Fin.elim0 i)]
        rw [Fintype.sum_option]
        have hwnone : w none = 1 := by simpa using hw1
        simp [hwnone]


section DependentBlocks

variable {D : E → Type*} [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
  [∀ e, Fintype (S e)]

theorem familyMember_le_piCylinderMin_familyMax
    (F : Set E → (∀ e, S e) → ℝ)
    (hF : ∀ K, PiDependsOn K (F K))
    (K : Set E) (x : ∀ e, S e) :
    F K x ≤ piCylinderMin (piFunctionalFamilyMax F) K x := by
  unfold piCylinderMin
  apply Finset.le_inf'
  intro y hy
  have hagree : piAgreeOn K x y := mem_piAgreementFiber.mp hy
  calc
    F K x = F K y := hF K hagree
    _ ≤ piFunctionalFamilyMax F y := by
      unfold piFunctionalFamilyMax
      exact Finset.le_sup' (fun L : Set E ↦ F L y) (Finset.mem_univ K)

theorem piFunctionalFamilyDisjointMaxAt_le_pi
    (F G : Set E → (∀ e, S e) → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K))
    (x y : ∀ e, S e) :
    piFunctionalFamilyDisjointMaxAt F G x y ≤
      piFunctionalDisjointMaxAt
        (piFunctionalFamilyMax F) (piFunctionalFamilyMax G) x y := by
  unfold piFunctionalFamilyDisjointMaxAt piFunctionalDisjointMaxAt
  apply Finset.sup'_le
  intro pair hpair
  have hleft : F pair.1 x ≤
      piCylinderMin (piFunctionalFamilyMax F) pair.1 x :=
    familyMember_le_piCylinderMin_familyMax F hF pair.1 x
  have hright : G pair.2 y ≤
      piCylinderMin (piFunctionalFamilyMax G) pair.2 y :=
    familyMember_le_piCylinderMin_familyMax G hG pair.2 y
  have hminF0 : 0 ≤ piCylinderMin (piFunctionalFamilyMax F) pair.1 x := by
    unfold piCylinderMin
    apply Finset.le_inf'
    intro z _
    exact piFunctionalFamilyMax_nonneg F hF0 z
  calc
    F pair.1 x * G pair.2 y ≤
        piCylinderMin (piFunctionalFamilyMax F) pair.1 x *
          piCylinderMin (piFunctionalFamilyMax G) pair.2 y :=
      mul_le_mul hleft hright (hG0 pair.2 y) hminF0
    _ ≤ (disjointCoordinatePairs E).sup'
        (disjointCoordinatePairs_nonempty (E := E))
        (fun p ↦ piCylinderMin (piFunctionalFamilyMax F) p.1 x *
          piCylinderMin (piFunctionalFamilyMax G) p.2 y) :=
      Finset.le_sup' (fun p : Set E × Set E ↦
        piCylinderMin (piFunctionalFamilyMax F) p.1 x *
          piCylinderMin (piFunctionalFamilyMax G) p.2 y) hpair


end DependentBlocks
end StatMech.FrontierA
