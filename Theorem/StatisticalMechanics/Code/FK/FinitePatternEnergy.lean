/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.CircuitLowerBound.Part6
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
open MeasureTheory Finset


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


variable (C : SimpleGraph V) [DecidableRel C.Adj]


theorem numClustersBC_setOpen_bounds (e : Sym2 V) (omega : ConfigSpace (Sym2 V)) :
    numClustersBC G C (setOpen e omega) ≤ numClustersBC G C (setClosed e omega) ∧
      numClustersBC G C (setClosed e omega) ≤
        numClustersBC G C (setOpen e omega) + 1 := by
  classical
  by_cases he : e ∈ G.edgeFinset
  · obtain ⟨a, b, hab, rfl⟩ : ∃ a b, G.Adj a b ∧ e = s(a, b) := by
      rw [SimpleGraph.mem_edgeFinset] at he
      induction e with
      | h a b => exact ⟨a, b, he, rfl⟩
    let H : SimpleGraph V := openSub G (setClosed s(a, b) omega) ⊔ C
    have hopen : openSub G (setOpen s(a, b) omega) ⊔ C =
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
    by_cases hr : H.Reachable a b
    · have hc := StatMech.Lattice.card_components_sup_edge_of_reachable H a b hr
      rw [numClustersBC, numClustersBC, hopen]
      change Nat.card (H ⊔ SimpleGraph.edge a b).ConnectedComponent ≤
          Nat.card H.ConnectedComponent ∧
        Nat.card H.ConnectedComponent ≤
          Nat.card (H ⊔ SimpleGraph.edge a b).ConnectedComponent + 1
      omega
    · have hc := StatMech.Lattice.card_components_sup_edge_of_not_reachable H a b hr
      rw [numClustersBC, numClustersBC, hopen]
      change Nat.card (H ⊔ SimpleGraph.edge a b).ConnectedComponent ≤
          Nat.card H.ConnectedComponent ∧
        Nat.card H.ConnectedComponent ≤
          Nat.card (H ⊔ SimpleGraph.edge a b).ConnectedComponent + 1
      omega
  · have hopen := openSub_setOpen_eq_setClosed_of_notMem G he omega
    have hc : numClustersBC G C (setOpen e omega) =
        numClustersBC G C (setClosed e omega) := by
      unfold numClustersBC
      rw [hopen]
    omega


theorem bcWeight_lo {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) (omega : ConfigSpace (Sym2 V)) :
    (1 - p) * bcWeight G C p q (setOpen e omega) ≤
      p * bcWeight G C p q (setClosed e omega) := by
  unfold bcWeight
  rw [edgeProduct_setOpen G p he, edgeProduct_setClosed G p he]
  set R := edgeRest G p e omega
  set k1 := numClustersBC G C (setOpen e omega)
  set k0 := numClustersBC G C (setClosed e omega)
  have hRpos : 0 < R := edgeRest_pos G hp hp1 e omega
  have hpow : q ^ k1 ≤ q ^ k0 :=
    pow_le_pow_right₀ hq (numClustersBC_setOpen_bounds G C e omega).1
  have hfac : (0 : ℝ) ≤ R * p * (1 - p) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpow hfac]


theorem bcWeight_hi {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) (omega : ConfigSpace (Sym2 V)) :
    p * bcWeight G C p q (setClosed e omega) ≤
      q * (1 - p) * bcWeight G C p q (setOpen e omega) := by
  unfold bcWeight
  rw [edgeProduct_setOpen G p he, edgeProduct_setClosed G p he]
  set R := edgeRest G p e omega
  set k1 := numClustersBC G C (setOpen e omega)
  set k0 := numClustersBC G C (setClosed e omega)
  have hRpos : 0 < R := edgeRest_pos G hp hp1 e omega
  have hpow : q ^ k0 ≤ q ^ (k1 + 1) :=
    pow_le_pow_right₀ hq (numClustersBC_setOpen_bounds G C e omega).2
  rw [pow_succ] at hpow
  have hfac : (0 : ℝ) ≤ R * p * (1 - p) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpow hfac]


theorem bcWeight_setOpen_ge {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 V) (omega : ConfigSpace (Sym2 V)) :
    cFE p q * (bcWeight G C p q (setOpen e omega) +
        bcWeight G C p q (setClosed e omega)) ≤
      bcWeight G C p q (setOpen e omega) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  by_cases he : e ∈ G.edgeFinset
  · set W1 := bcWeight G C p q (setOpen e omega)
    set W0 := bcWeight G C p q (setClosed e omega)
    have hW1pos : 0 < W1 := bcWeight_pos G C hp hp1 hq0 _
    have hW0pos : 0 < W0 := bcWeight_pos G C hp hp1 hq0 _
    have hhi : p * W0 ≤ q * (1 - p) * W1 := bcWeight_hi G C hp hp1 hq he omega
    have hden : 0 < p + q * (1 - p) := by nlinarith
    have hkey : (p / (p + q * (1 - p))) * (W1 + W0) ≤ W1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith
    have hcfe : cFE p q ≤ p / (p + q * (1 - p)) := min_le_left _ _
    have hsum : 0 ≤ W1 + W0 := by positivity
    exact (mul_le_mul_of_nonneg_right hcfe hsum).trans hkey
  · have hep : edgeProduct G p (setOpen e omega) =
        edgeProduct G p (setClosed e omega) := by
      unfold edgeProduct
      apply Finset.prod_congr rfl
      intro e' he'
      have hne : e' ≠ e := fun h => he (h ▸ he')
      rw [setOpen_of_ne hne, setClosed_of_ne hne]
    have hk : numClustersBC G C (setOpen e omega) =
        numClustersBC G C (setClosed e omega) := by
      unfold numClustersBC
      rw [openSub_setOpen_eq_setClosed_of_notMem G he omega]
    have hweq : bcWeight G C p q (setOpen e omega) =
        bcWeight G C p q (setClosed e omega) := by
      unfold bcWeight
      rw [hep, hk]
    have hcfe : cFE p q ≤ 1 / 2 := cFE_le_half hp hp1 hq
    have hW1pos : 0 < bcWeight G C p q (setOpen e omega) :=
      bcWeight_pos G C hp hp1 hq0 _
    rw [← hweq]
    nlinarith [mul_le_mul_of_nonneg_right hcfe
      (by positivity : 0 ≤ bcWeight G C p q (setOpen e omega) +
        bcWeight G C p q (setOpen e omega))]


theorem bcWeight_setClosed_ge {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 V) (omega : ConfigSpace (Sym2 V)) :
    cFE p q * (bcWeight G C p q (setOpen e omega) +
        bcWeight G C p q (setClosed e omega)) ≤
      bcWeight G C p q (setClosed e omega) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  by_cases he : e ∈ G.edgeFinset
  · have hW1pos : 0 < bcWeight G C p q (setOpen e omega) :=
      bcWeight_pos G C hp hp1 hq0 _
    have hW0pos : 0 < bcWeight G C p q (setClosed e omega) :=
      bcWeight_pos G C hp hp1 hq0 _
    have hlo : (1 - p) * bcWeight G C p q (setOpen e omega) ≤
        p * bcWeight G C p q (setClosed e omega) :=
      bcWeight_lo G C hp hp1 hq he omega
    have hcfe : cFE p q ≤ 1 - p := min_le_right _ _
    have hkey : (1 - p) * (bcWeight G C p q (setOpen e omega) +
          bcWeight G C p q (setClosed e omega)) ≤
        bcWeight G C p q (setClosed e omega) := by
      nlinarith
    have hsum : 0 ≤ bcWeight G C p q (setOpen e omega) +
        bcWeight G C p q (setClosed e omega) := by positivity
    exact (mul_le_mul_of_nonneg_right hcfe hsum).trans hkey
  · have hep : edgeProduct G p (setOpen e omega) =
        edgeProduct G p (setClosed e omega) := by
      unfold edgeProduct
      apply Finset.prod_congr rfl
      intro e' he'
      have hne : e' ≠ e := fun h => he (h ▸ he')
      rw [setOpen_of_ne hne, setClosed_of_ne hne]
    have hk : numClustersBC G C (setOpen e omega) =
        numClustersBC G C (setClosed e omega) := by
      unfold numClustersBC
      rw [openSub_setOpen_eq_setClosed_of_notMem G he omega]
    have hweq : bcWeight G C p q (setOpen e omega) =
        bcWeight G C p q (setClosed e omega) := by
      unfold bcWeight
      rw [hep, hk]
    have hcfe : cFE p q ≤ 1 / 2 := cFE_le_half hp hp1 hq
    have hW0pos : 0 < bcWeight G C p q (setClosed e omega) :=
      bcWeight_pos G C hp hp1 hq0 _
    rw [hweq]
    nlinarith [mul_le_mul_of_nonneg_right hcfe
      (by positivity : 0 ≤ bcWeight G C p q (setClosed e omega) +
        bcWeight G C p q (setClosed e omega))]

variable {C}


theorem fkWeight_setOpen_ge {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 V) (omega : ConfigSpace (Sym2 V)) :
    cFE p q * (fkWeight G p q (setOpen e omega) + fkWeight G p q (setClosed e omega)) ≤
      fkWeight G p q (setOpen e omega) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hsum : 0 < fkWeight G p q (setOpen e omega) +
      fkWeight G p q (setClosed e omega) := by
    exact add_pos (fkWeight_pos G hp hp1 hq0 _) (fkWeight_pos G hp hp1 hq0 _)
  have hfe := (finite_energy G hp hp1 hq e omega).1
  rw [condOpen_eq_weightRatio G hp hp1 hq0] at hfe
  rwa [le_div_iff₀ hsum] at hfe


end FK
end StatMech
