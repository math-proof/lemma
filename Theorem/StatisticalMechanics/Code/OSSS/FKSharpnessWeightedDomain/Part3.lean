/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodic.Part3
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomain.Part3
open scoped BigOperators Classical
open Finset Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (C : SimpleGraph V) [DecidableRel C.Adj]


theorem condBcProbW_nonneg {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (F : Finset (Sym2 V))
    (psi : ConfigSpace (Sym2 V)) :
    (0 : ConfigSpace (Sym2 V) -> Real) <= condBcProbW G C pf q F psi := by
  intro omega
  unfold condBcProbW
  split
  · exact div_nonneg (bcWeightW_nonneg G C hpf hpf1 hq omega)
      (inducedBcZW_pos G C hpf hpf1 hq F psi).le
  · rfl

theorem condBcProbW_sum_eq_one {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (F : Finset (Sym2 V))
    (psi : ConfigSpace (Sym2 V)) :
    ∑ omega, condBcProbW G C pf q F psi omega = 1 := by
  unfold condBcProbW
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.sum_div]
  exact div_self (inducedBcZW_pos G C hpf hpf1 hq F psi).ne'

theorem condBcProbW_cross_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) (F : Finset (Sym2 V))
    (psi a b : ConfigSpace (Sym2 V)) :
    condBcProbW G C pf q F psi a * condBcProbW G C' pf q F psi b <=
      condBcProbW G C pf q F psi (a ⊓ b) *
        condBcProbW G C' pf q F psi (a ⊔ b) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hright : 0 <=
      condBcProbW G C pf q F psi (a ⊓ b) *
        condBcProbW G C' pf q F psi (a ⊔ b) :=
    mul_nonneg (condBcProbW_nonneg G C hpf hpf1 hq0 F psi _)
      (condBcProbW_nonneg G C' hpf hpf1 hq0 F psi _)
  unfold condBcProbW
  by_cases ha : AgreesOff F psi a
  · by_cases hb : AgreesOff F psi b
    · rw [if_pos ha, if_pos hb, if_pos (agreesOff_inf ha hb),
        if_pos (agreesOff_sup ha hb), div_mul_div_comm, div_mul_div_comm,
        div_le_div_iff_of_pos_right
          (mul_pos (inducedBcZW_pos G C hpf hpf1 hq0 F psi)
            (inducedBcZW_pos G C' hpf hpf1 hq0 F psi))]
      exact bcWeightW_cross_bc G C C' hCC' hpf hpf1 hq a b
    · rw [if_neg hb, mul_zero]
      simpa only [condBcProbW] using hright
  · rw [if_neg ha, zero_mul]
    simpa only [condBcProbW] using hright


theorem condBcProbW_mono_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) (F : Finset (Sym2 V))
    (psi : ConfigSpace (Sym2 V))
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        condBcProbW G C pf q F psi omega) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        condBcProbW G C' pf q F psi omega := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact condBcProbW_nonneg G C hpf hpf1 hq0 F psi
  · exact condBcProbW_nonneg G C' hpf hpf1 hq0 F psi
  · rw [condBcProbW_sum_eq_one G C hpf hpf1 hq0 F psi,
      condBcProbW_sum_eq_one G C' hpf hpf1 hq0 F psi]
  · exact fun a b =>
      condBcProbW_cross_bc G C C' hCC' hpf hpf1 hq F psi a b


theorem activeBCProb_mono_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q)
    {A : Set (ConfigSpace G.edgeSet)} (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        activeBCProb G C pf q omega) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        activeBCProb G C' pf q omega := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact fun omega => (activeBCProb_pos G C hpf hpf1 hq0 omega).le
  · exact fun omega => (activeBCProb_pos G C' hpf hpf1 hq0 omega).le
  · rw [activeBCProb_sum_eq_one G C hpf hpf1 hq0,
      activeBCProb_sum_eq_one G C' hpf hpf1 hq0]
  · intro a b
    have hcluster :
        q ^ numClustersBC G C (extendActive G a) *
            q ^ numClustersBC G C' (extendActive G b) <=
          q ^ numClustersBC G C (extendActive G (a ⊓ b)) *
            q ^ numClustersBC G C' (extendActive G (a ⊔ b)) := by
      rw [extendActive_inf, extendActive_sup, ← pow_add, ← pow_add]
      exact pow_le_pow_right₀ hq
        (mixed_supermodular_bc G C C' hCC' (extendActive G a) (extendActive G b))
    have hedge := edgeProductW_logModular G pf
      (extendActive G a) (extendActive G b)
    have hedge' : edgeProductW G pf (extendActive G a) *
        edgeProductW G pf (extendActive G b) =
          edgeProductW G pf (extendActive G (a ⊓ b)) *
            edgeProductW G pf (extendActive G (a ⊔ b)) := by
      rw [hedge, extendActive_inf, extendActive_sup]
      ring
    have hedge0 : 0 <= edgeProductW G pf (extendActive G (a ⊓ b)) *
        edgeProductW G pf (extendActive G (a ⊔ b)) :=
      mul_nonneg (edgeProductW_pos G hpf hpf1 _).le
        (edgeProductW_pos G hpf hpf1 _).le
    have hweight : activeBCWeight G C pf q a * activeBCWeight G C' pf q b <=
        activeBCWeight G C pf q (a ⊓ b) * activeBCWeight G C' pf q (a ⊔ b) := by
      unfold activeBCWeight
      calc
        (edgeProductW G pf (extendActive G a) *
              q ^ numClustersBC G C (extendActive G a)) *
            (edgeProductW G pf (extendActive G b) *
              q ^ numClustersBC G C' (extendActive G b)) =
          (edgeProductW G pf (extendActive G a) *
              edgeProductW G pf (extendActive G b)) *
            (q ^ numClustersBC G C (extendActive G a) *
              q ^ numClustersBC G C' (extendActive G b)) := by ring
        _ = (edgeProductW G pf (extendActive G (a ⊓ b)) *
              edgeProductW G pf (extendActive G (a ⊔ b))) *
            (q ^ numClustersBC G C (extendActive G a) *
              q ^ numClustersBC G C' (extendActive G b)) := by
            rw [hedge']
        _ <= (edgeProductW G pf (extendActive G (a ⊓ b)) *
              edgeProductW G pf (extendActive G (a ⊔ b))) *
            (q ^ numClustersBC G C (extendActive G (a ⊓ b)) *
              q ^ numClustersBC G C' (extendActive G (a ⊔ b))) :=
            mul_le_mul_of_nonneg_left hcluster hedge0
        _ = (edgeProductW G pf (extendActive G (a ⊓ b)) *
              q ^ numClustersBC G C (extendActive G (a ⊓ b))) *
            (edgeProductW G pf (extendActive G (a ⊔ b)) *
              q ^ numClustersBC G C' (extendActive G (a ⊔ b))) := by ring
    have hZ : 0 < activeBCZ G C pf q := activeBCZ_pos G C hpf hpf1 hq0
    have hZ' : 0 < activeBCZ G C' pf q := activeBCZ_pos G C' hpf hpf1 hq0
    unfold activeBCProb
    rw [div_mul_div_comm, div_mul_div_comm,
      div_le_div_iff_of_pos_right (mul_pos hZ hZ')]
    exact hweight


theorem bcWeightW_eq_of_edges (pf : Sym2 V -> Real) (q : Real)
    (omega eta : ConfigSpace (Sym2 V))
    (h : forall e, e ∈ G.edgeFinset -> omega e = eta e) :
    bcWeightW G C pf q omega = bcWeightW G C pf q eta := by
  unfold bcWeightW
  rw [numClustersBC_eq_of_edges G C omega eta h]
  congr 1
  unfold edgeProductW
  exact Finset.prod_congr rfl (fun e he => by rw [h e he])

theorem bcWeightW_activeSplitEquiv_symm (pf : Sym2 V -> Real) (q : Real)
    (eta : ConfigSpace G.edgeSet)
    (xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet}) :
    bcWeightW G C pf q ((activeSplitEquiv G).symm (eta, xi)) =
      activeBCWeight G C pf q eta := by
  apply bcWeightW_eq_of_edges G C
  intro e he
  have heSet : e ∈ G.edgeSet := by
    rwa [← SimpleGraph.mem_edgeFinset]
  rw [show ((activeSplitEquiv G).symm (eta, xi)) e = eta ⟨e, heSet⟩ by
    simp [activeSplitEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, heSet]]
  exact (extendActive_apply G eta ⟨e, heSet⟩).symm

theorem activeBCZW_factorization (pf : Sym2 V -> Real) (q : Real) :
    bcZW G C pf q = 2 ^ ecz_NE G * activeBCZ G C pf q := by
  rw [bcZW, ← Equiv.sum_comp (activeSplitEquiv G).symm
    (fun omega => bcWeightW G C pf q omega), Fintype.sum_prod_type]
  have key : forall eta : ConfigSpace G.edgeSet,
      (∑ xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet},
        bcWeightW G C pf q ((activeSplitEquiv G).symm (eta, xi))) =
      2 ^ ecz_NE G * activeBCWeight G C pf q eta := by
    intro eta
    rw [Finset.sum_congr rfl (fun xi _ =>
      bcWeightW_activeSplitEquiv_symm G C pf q eta xi)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_inactive_config G]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun eta _ => key eta), ← Finset.mul_sum]
  rfl

theorem activeBCNumerW_factorization (pf : Sym2 V -> Real) (q : Real)
    (f : ConfigSpace G.edgeSet -> Real) :
    (∑ omega : ConfigSpace (Sym2 V),
      f (restrictActive G omega) * bcWeightW G C pf q omega) =
      2 ^ ecz_NE G * activeBCNumer G C pf q f := by
  rw [← Equiv.sum_comp (activeSplitEquiv G).symm
    (fun omega => f (restrictActive G omega) * bcWeightW G C pf q omega),
    Fintype.sum_prod_type]
  have key : forall eta : ConfigSpace G.edgeSet,
      (∑ xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet},
        f (restrictActive G ((activeSplitEquiv G).symm (eta, xi))) *
          bcWeightW G C pf q ((activeSplitEquiv G).symm (eta, xi))) =
      2 ^ ecz_NE G * (f eta * activeBCWeight G C pf q eta) := by
    intro eta
    rw [Finset.sum_congr rfl (fun xi _ => by
      rw [restrictActive_activeSplitEquiv_symm,
        bcWeightW_activeSplitEquiv_symm G C pf q eta xi])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_inactive_config G]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun eta _ => key eta), ← Finset.mul_sum]
  rfl


theorem activeBCMean_eq_bcProbW_lift {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (f : ConfigSpace G.edgeSet -> Real) :
    activeBCMean G C pf q f =
      ∑ omega : ConfigSpace (Sym2 V),
        f (restrictActive G omega) * bcProbW G C pf q omega := by
  have htwo : (2 : Real) ^ ecz_NE G ≠ 0 := by positivity
  have hZactive : activeBCZ G C pf q ≠ 0 :=
    (activeBCZ_pos G C hpf hpf1 hq).ne'
  rw [activeBCMean_eq_div]
  unfold bcProbW
  rw [show (fun omega : ConfigSpace (Sym2 V) =>
      f (restrictActive G omega) *
        (bcWeightW G C pf q omega / bcZW G C pf q)) =
      (fun omega =>
        (f (restrictActive G omega) * bcWeightW G C pf q omega) /
          bcZW G C pf q) by funext omega; ring]
  rw [← Finset.sum_div, activeBCNumerW_factorization G C,
    activeBCZW_factorization G C]
  field_simp


end FK
end StatMech
