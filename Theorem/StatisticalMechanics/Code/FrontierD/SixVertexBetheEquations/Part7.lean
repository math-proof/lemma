/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part12
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexClosedRootSimplex_nonempty (n : ℕ) :
    Set.Nonempty {p : Fin n → ℝ | SixVertexClosedRootSimplex p} := by
  refine ⟨fun _ => 0, ?_⟩
  constructor
  · exact fun _ _ _ => le_rfl
  constructor
  · intro j
    simp
  · intro j
    exact ⟨(neg_lt_zero.mpr Real.pi_pos).le, Real.pi_pos.le⟩

theorem convex_sixVertexClosedRootSimplex (n : ℕ) :
    Convex ℝ {p : Fin n → ℝ | SixVertexClosedRootSimplex p} := by
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨hpmono, hpsymm, hpint⟩
  rcases hq with ⟨hqmono, hqsymm, hqint⟩
  constructor
  · intro i j hij
    change a * p i + b * q i ≤ a * p j + b * q j
    exact add_le_add (mul_le_mul_of_nonneg_left (hpmono hij) ha)
      (mul_le_mul_of_nonneg_left (hqmono hij) hb)
  constructor
  · intro j
    change a * p j.rev + b * q j.rev = -(a * p j + b * q j)
    rw [hpsymm, hqsymm]
    ring
  · intro j
    change -Real.pi ≤ a * p j + b * q j ∧
      a * p j + b * q j ≤ Real.pi
    constructor <;> nlinarith [(hpint j).1, (hpint j).2,
      (hqint j).1, (hqint j).2]

theorem isClosed_sixVertexClosedRootSimplex (n : ℕ) :
    IsClosed {p : Fin n → ℝ | SixVertexClosedRootSimplex p} := by
  have hmono : IsClosed {p : Fin n → ℝ | Monotone p} := isClosed_monotone
  have hsymm : IsClosed {p : Fin n → ℝ | SixVertexRootSymmetric p} := by
    have heq : {p : Fin n → ℝ | SixVertexRootSymmetric p} =
        ⋂ j, {p | p j.rev = -p j} := by
      ext p
      simp [SixVertexRootSymmetric]
    rw [heq]
    apply isClosed_iInter
    intro j
    exact isClosed_eq (continuous_apply j.rev) (continuous_apply j).neg
  have hinterval : IsClosed {p : Fin n → ℝ |
      ∀ j, -Real.pi ≤ p j ∧ p j ≤ Real.pi} := by
    have heq : {p : Fin n → ℝ | ∀ j, -Real.pi ≤ p j ∧ p j ≤ Real.pi} =
        ⋂ j, ({p | -Real.pi ≤ p j} ∩ {p | p j ≤ Real.pi}) := by
      ext p
      simp
    rw [heq]
    apply isClosed_iInter
    intro j
    exact (isClosed_le continuous_const (continuous_apply j)).inter
      (isClosed_le (continuous_apply j) continuous_const)
  simpa only [SixVertexClosedRootSimplex, Set.setOf_and] using
    hmono.inter (hsymm.inter hinterval)

theorem isCompact_sixVertexClosedRootSimplex (n : ℕ) :
    IsCompact {p : Fin n → ℝ | SixVertexClosedRootSimplex p} := by
  have hcube : IsCompact
      (Set.pi Set.univ fun _ : Fin n => Set.Icc (-Real.pi) Real.pi) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  apply hcube.of_isClosed_subset (isClosed_sixVertexClosedRootSimplex n)
  intro p hp
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
  exact fun j => (hp.2.2 j)

theorem sixVertexBetheUpdate_closed_to_open {c : ℝ} (hc : 2 < c)
    {N n : ℕ} (hhalf : 2 * n ≤ N) {p : Fin n → ℝ}
    (hp : SixVertexClosedRootSimplex p) :
    SixVertexOpenRootSimplex (sixVertexBetheUpdate c N n p) := by
  rcases hp with ⟨hmono, hsymm, hinterval⟩
  constructor
  · by_cases hn : n = 0
    · subst n
      exact fun i => Fin.elim0 i
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hN : 0 < N := lt_of_lt_of_le (by omega : 0 < 2 * n) hhalf
      exact sixVertexBetheUpdate_strictMono_of_monotone hc hN hmono
  constructor
  · exact sixVertexBetheUpdate_symmetric c hsymm
  · intro j
    have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
    have hN : 0 < N := lt_of_lt_of_le (by omega : 0 < 2 * n) hhalf
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hsumPi := sum_sixVertexTheta_pi_of_symmetric c hsymm
    have hsumNegPi := sum_sixVertexTheta_neg_pi_of_symmetric c hsymm
    have hsumUpper :
        (∑ k, sixVertexTheta c Real.pi (p k)) ≤
          ∑ k, sixVertexTheta c (p j) (p k) := by
      apply Finset.sum_le_sum
      intro k _
      exact (strictAnti_sixVertexTheta_left hc (p k)).antitone (hinterval j).2
    have hsumLower :
        (∑ k, sixVertexTheta c (p j) (p k)) ≤
          ∑ k, sixVertexTheta c (-Real.pi) (p k) := by
      apply Finset.sum_le_sum
      intro k _
      exact (strictAnti_sixVertexTheta_left hc (p k)).antitone (hinterval j).1
    have hjlt : (j.val : ℝ) < n := by exact_mod_cast j.isLt
    have hjstep : (j.val : ℝ) + 1 ≤ (n : ℝ) := by
      have hjint : (j.val : ℤ) < n := by exact_mod_cast j.isLt
      exact_mod_cast hjint
    have hIupper : sixVertexCentralQuantumNumber j ≤ ((n : ℝ) - 1) / 2 := by
      rw [sixVertexCentralQuantumNumber_eq]
      linarith
    have hIlower : -((n : ℝ) - 1) / 2 ≤ sixVertexCentralQuantumNumber j := by
      rw [sixVertexCentralQuantumNumber_eq]
      have hjnonneg : (0 : ℝ) ≤ j.val := by positivity
      linarith
    have hhalfre : (2 : ℝ) * (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hhalf
    have hcount : (2 : ℝ) * (n : ℝ) - 1 < (N : ℝ) := by
      have hnre : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    unfold sixVertexBetheUpdate
    constructor
    · apply (lt_div_iff₀ hNreal).mpr
      rw [hsumNegPi] at hsumLower
      nlinarith [Real.pi_pos]
    · apply (div_lt_iff₀ hNreal).mpr
      rw [hsumPi] at hsumUpper
      nlinarith [Real.pi_pos]

theorem SixVertexOpenRootSimplex.toClosed {n : ℕ} {p : Fin n → ℝ}
    (hp : SixVertexOpenRootSimplex p) : SixVertexClosedRootSimplex p := by
  rcases hp with ⟨hmono, hsymm, hinterval⟩
  exact ⟨hmono.monotone, hsymm, fun j =>
    ⟨(hinterval j).1.le, (hinterval j).2.le⟩⟩

theorem sixVertexBetheUpdate_mapsTo_closedRootSimplex {c : ℝ}
    (hc : 2 < c) {N n : ℕ} (hhalf : 2 * n ≤ N) :
    Set.MapsTo (sixVertexBetheUpdate c N n)
      {p | SixVertexClosedRootSimplex p}
      {p | SixVertexClosedRootSimplex p} := by
  intro p hp
  exact (sixVertexBetheUpdate_closed_to_open hc hhalf hp).toClosed

theorem sixVertexBetheUpdate_fixedPoint_mem_open {c : ℝ}
    (hc : 2 < c) {N n : ℕ} (hhalf : 2 * n ≤ N)
    {p : Fin n → ℝ} (hp : SixVertexClosedRootSimplex p)
    (hfix : sixVertexBetheUpdate c N n p = p) :
    SixVertexOpenRootSimplex p := by
  rw [← hfix]
  exact sixVertexBetheUpdate_closed_to_open hc hhalf hp

theorem sixVertexBetheUpdate_fixedPoint_is_solution {c : ℝ}
    {N n : ℕ} (hN : 0 < N) {p : Fin n → ℝ}
    (hfix : sixVertexBetheUpdate c N n p = p) :
    SixVertexSatisfiesBetheEquations c N n p :=
  (sixVertexBetheUpdate_eq_self_iff hN p).mp hfix

theorem sum_sixVertexTheta_pair (c : ℝ) {n : ℕ} (p : Fin n → ℝ) :
    ∑ j, ∑ k, sixVertexTheta c (p j) (p k) = 0 := by
  let S := ∑ j, ∑ k, sixVertexTheta c (p j) (p k)
  have hneg : S = -S := by
    calc
      S = ∑ j, ∑ k, -sixVertexTheta c (p k) (p j) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        exact sixVertexTheta_antisymm c (p k) (p j)
      _ = -(∑ j, ∑ k, sixVertexTheta c (p k) (p j)) := by
        simp
      _ = -S := by
        rw [Finset.sum_comm]
  linarith


theorem SixVertexSatisfiesBetheEquations.sum_eq_zero
    {c : ℝ} {N n : ℕ} (hN : 0 < N) {p : Fin n → ℝ}
    (hp : SixVertexSatisfiesBetheEquations c N n p) :
    ∑ j, p j = 0 := by
  have hsum :
      (∑ j, (N : ℝ) * p j) =
        ∑ j, (2 * Real.pi * sixVertexCentralQuantumNumber j -
          ∑ k, sixVertexTheta c (p j) (p k)) := by
    exact Finset.sum_congr rfl (fun j _ => hp j)
  have htheta := sum_sixVertexTheta_pair c p
  have hquantum := sum_sixVertexCentralQuantumNumber n
  simp only [Finset.sum_sub_distrib] at hsum
  rw [← Finset.mul_sum] at hsum
  rw [← Finset.mul_sum] at hsum
  rw [hquantum, mul_zero, htheta, sub_zero] at hsum
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith


theorem SixVertexSatisfiesBetheEquations.reverse_neg
    {c : ℝ} {N n : ℕ} {p : Fin n → ℝ}
    (hp : SixVertexSatisfiesBetheEquations c N n p) :
    SixVertexSatisfiesBetheEquations c N n (fun j => -p j.rev) := by
  intro j
  have hsum :
      (∑ k : Fin n, sixVertexTheta c (p j.rev) (p k.rev)) =
        ∑ k : Fin n, sixVertexTheta c (p j.rev) (p k) := by
    apply Fintype.sum_equiv Fin.revPerm
    intro k
    rfl
  have hj := hp j.rev
  rw [sixVertexCentralQuantumNumber_rev] at hj
  simp only [sixVertexTheta_neg]
  rw [Finset.sum_neg_distrib, hsum]
  nlinarith

end
end StatMech.FrontierD
