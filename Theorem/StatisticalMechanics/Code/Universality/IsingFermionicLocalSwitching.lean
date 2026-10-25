/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part8
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingDobrushinDomain

theorem fkIsingCriticalParameter_eq_sqrtTwo_mul_one_sub :
    fkIsingCriticalParameter =
      Real.sqrt 2 * (1 - fkIsingCriticalParameter) := by
  unfold fkIsingCriticalParameter selfDualPoint
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  field_simp
  nlinarith

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]

variable (D : FKIsingDobrushinDomain P M)

theorem windingPhase_eq_exp_turn_mul
    (omega omega' : ConfigSpace (Sym2 P.V)) (e e' : M) (turn : Real)
    (h : D.winding omega' e' = D.winding omega e + turn) :
    D.windingPhase omega' e' =
      Complex.exp (Complex.I * ((turn / 2 : Real) : Complex)) *
        D.windingPhase omega e := by
  unfold windingPhase
  rw [h, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem exp_isHalf_turn_pi_div_two_eq_isingLambda :
    Complex.exp (Complex.I * (((Real.pi / 2) / 2 : Real) : Complex)) =
      isingLambda := by
  unfold isingLambda
  congr 1
  push_cast
  ring

theorem exp_isHalf_turn_pi_eq_isingLambda_sq :
    Complex.exp (Complex.I * ((Real.pi / 2 : Real) : Complex)) =
      isingLambda ^ 2 := by
  rw [isingLambda_sq]
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem exp_isHalf_turn_neg_pi_div_two_eq_isingLambda_inv :
    Complex.exp
        (Complex.I * (((-(Real.pi / 2)) / 2 : Real) : Complex)) =
      isingLambda⁻¹ := by
  rw [show ((-(Real.pi / 2)) / 2 : Real) = -(Real.pi / 4) by ring]
  rw [show Complex.I * ((-(Real.pi / 4) : Real) : Complex) =
    -(((Real.pi / 4 : Real) : Complex) * Complex.I) by push_cast; ring]
  rw [Complex.exp_neg]
  rfl


theorem criticalMass_setOpen_eq_sqrtTwo_mul_setClosed_of_clusterCount_eq
    {e : Sym2 P.V} (he : e ∈ P.G.edgeFinset)
    (omega : ConfigSpace (Sym2 P.V))
    (hcluster : numClustersBC P.G D.wiring (setOpen e omega) =
      numClustersBC P.G D.wiring (setClosed e omega)) :
    D.criticalMass (setOpen e omega) =
      Real.sqrt 2 * D.criticalMass (setClosed e omega) := by
  unfold criticalMass bcProb bcWeight
  rw [edgeProduct_setOpen P.G fkIsingCriticalParameter he,
    edgeProduct_setClosed P.G fkIsingCriticalParameter he, hcluster]
  let A := edgeRest P.G fkIsingCriticalParameter e omega *
    2 ^ numClustersBC P.G D.wiring (setClosed e omega) /
      bcZ P.G D.wiring fkIsingCriticalParameter 2
  calc
    edgeRest P.G fkIsingCriticalParameter e omega * fkIsingCriticalParameter *
          2 ^ numClustersBC P.G D.wiring (setClosed e omega) /
        bcZ P.G D.wiring fkIsingCriticalParameter 2 =
      fkIsingCriticalParameter * A := by simp only [A]; ring
    _ = (Real.sqrt 2 * (1 - fkIsingCriticalParameter)) * A :=
      congrArg (fun x : Real => x * A)
        fkIsingCriticalParameter_eq_sqrtTwo_mul_one_sub
    _ = Real.sqrt 2 *
        (edgeRest P.G fkIsingCriticalParameter e omega *
          (1 - fkIsingCriticalParameter) *
          2 ^ numClustersBC P.G D.wiring (setClosed e omega) /
          bcZ P.G D.wiring fkIsingCriticalParameter 2) := by
      simp only [A]
      ring


theorem sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge
    {e : Sym2 P.V} (he : e ∈ P.G.edgeFinset)
    (omega : ConfigSpace (Sym2 P.V))
    (hcluster : numClustersBC P.G D.wiring (setClosed e omega) =
      numClustersBC P.G D.wiring (setOpen e omega) + 1) :
    Real.sqrt 2 * D.criticalMass (setOpen e omega) =
      D.criticalMass (setClosed e omega) := by
  unfold criticalMass bcProb bcWeight
  rw [edgeProduct_setOpen P.G fkIsingCriticalParameter he,
    edgeProduct_setClosed P.G fkIsingCriticalParameter he, hcluster, pow_succ]
  let A := edgeRest P.G fkIsingCriticalParameter e omega *
    2 ^ numClustersBC P.G D.wiring (setOpen e omega) /
      bcZ P.G D.wiring fkIsingCriticalParameter 2
  have hp : Real.sqrt 2 * fkIsingCriticalParameter =
      2 * (1 - fkIsingCriticalParameter) := by
    calc
      Real.sqrt 2 * fkIsingCriticalParameter =
          Real.sqrt 2 * (Real.sqrt 2 * (1 - fkIsingCriticalParameter)) :=
        congrArg (fun x : Real => Real.sqrt 2 * x)
          fkIsingCriticalParameter_eq_sqrtTwo_mul_one_sub
      _ = 2 * (1 - fkIsingCriticalParameter) := by
        rw [← mul_assoc, show Real.sqrt 2 * Real.sqrt 2 = 2 by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) <= 2)]]
  calc
    Real.sqrt 2 *
        (edgeRest P.G fkIsingCriticalParameter e omega *
          fkIsingCriticalParameter *
          2 ^ numClustersBC P.G D.wiring (setOpen e omega) /
          bcZ P.G D.wiring fkIsingCriticalParameter 2) =
      (Real.sqrt 2 * fkIsingCriticalParameter) * A := by
        simp only [A]
        ring
    _ = (2 * (1 - fkIsingCriticalParameter)) * A :=
      congrArg (fun x : Real => x * A) hp
    _ = edgeRest P.G fkIsingCriticalParameter e omega *
        (1 - fkIsingCriticalParameter) *
        (2 ^ numClustersBC P.G D.wiring (setOpen e omega) * 2) /
        bcZ P.G D.wiring fkIsingCriticalParameter 2 := by
      simp only [A]
      ring


theorem numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable
    (a b : P.V) (hab : P.G.Adj a b)
    (omega : ConfigSpace (Sym2 P.V))
    (hnot : ¬(openSub P.G (setClosed s(a, b) omega) ⊔ D.wiring).Reachable a b) :
    numClustersBC P.G D.wiring (setClosed s(a, b) omega) =
      numClustersBC P.G D.wiring (setOpen s(a, b) omega) + 1 := by
  let H := openSub P.G (setClosed s(a, b) omega) ⊔ D.wiring
  have hopen : openSub P.G (setOpen s(a, b) omega) ⊔ D.wiring =
      H ⊔ SimpleGraph.edge a b := by
    ext x y
    simp only [H, SimpleGraph.sup_adj, openSub_adj, SimpleGraph.edge_adj]
    constructor
    · rintro (⟨hxy, hopen⟩ | hC)
      · by_cases hxyab : s(x, y) = s(a, b)
        · rw [Sym2.eq_iff] at hxyab
          rcases hxyab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hab.ne⟩
          · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hab.ne.symm⟩
        · have hopen' := hopen
          rw [setOpen_of_ne hxyab] at hopen'
          rw [setClosed_of_ne hxyab]
          exact Or.inl (Or.inl ⟨hxy, hopen'⟩)
      · exact Or.inl (Or.inr hC)
    · rintro ((⟨hxy, hclosed⟩ | hC) | hedge)
      · exact Or.inl ⟨hxy, by
          by_cases hxyab : s(x, y) = s(a, b)
          · rw [hxyab]
            simp
          · rw [setClosed_of_ne hxyab] at hclosed
            rw [setOpen_of_ne hxyab]
            exact hclosed⟩
      · exact Or.inr hC
      · rcases hedge.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨hab, by simp⟩
        · exact Or.inl ⟨hab.symm, by rw [Sym2.eq_swap]; simp⟩
  have hcount := StatMech.Lattice.card_components_sup_edge_of_not_reachable
    H a b hnot
  unfold numClustersBC
  rw [hopen]
  exact hcount.symm


theorem numClustersBC_setOpen_eq_setClosed_of_reachable
    (a b : P.V) (hab : P.G.Adj a b)
    (omega : ConfigSpace (Sym2 P.V))
    (hreach : (openSub P.G (setClosed s(a, b) omega) ⊔ D.wiring).Reachable a b) :
    numClustersBC P.G D.wiring (setOpen s(a, b) omega) =
      numClustersBC P.G D.wiring (setClosed s(a, b) omega) := by
  let H := openSub P.G (setClosed s(a, b) omega) ⊔ D.wiring
  have hopen : openSub P.G (setOpen s(a, b) omega) ⊔ D.wiring =
      H ⊔ SimpleGraph.edge a b := by
    ext x y
    simp only [H, SimpleGraph.sup_adj, openSub_adj, SimpleGraph.edge_adj]
    constructor
    · rintro (⟨hxy, hopen⟩ | hC)
      · by_cases hxyab : s(x, y) = s(a, b)
        · rw [Sym2.eq_iff] at hxyab
          rcases hxyab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hab.ne⟩
          · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hab.ne.symm⟩
        · have hopen' := hopen
          rw [setOpen_of_ne hxyab] at hopen'
          rw [setClosed_of_ne hxyab]
          exact Or.inl (Or.inl ⟨hxy, hopen'⟩)
      · exact Or.inl (Or.inr hC)
    · rintro ((⟨hxy, hclosed⟩ | hC) | hedge)
      · exact Or.inl ⟨hxy, by
          by_cases hxyab : s(x, y) = s(a, b)
          · rw [hxyab]
            simp
          · rw [setClosed_of_ne hxyab] at hclosed
            rw [setOpen_of_ne hxyab]
            exact hclosed⟩
      · exact Or.inr hC
      · rcases hedge.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨hab, by simp⟩
        · exact Or.inl ⟨hab.symm, by rw [Sym2.eq_swap]; simp⟩
  have hcount := StatMech.Lattice.card_components_sup_edge_of_reachable
    H a b hreach
  unfold numClustersBC
  rw [hopen]
  exact hcount


end FKIsingDobrushinDomain
end
end StatMech.Universality
