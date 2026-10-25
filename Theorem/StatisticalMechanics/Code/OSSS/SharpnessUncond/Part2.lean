/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.SharpnessFK
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part7
import Theorem.StatisticalMechanics.Code.OSSS.TreeComplete.Part5
import Theorem.StatisticalMechanics.Code.FK.RussoDerivative.Part5
import Def.StatisticalMechanics.Code.OSSS.SharpnessUncond
open scoped BigOperators
open Finset
open Real Set
open StatMech.Lattice

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

open StatMech.OSSS

open StatMech.OSSS.CovLowerBound

open StatMech.OSSS.SharpnessFK

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.TreeComplete

open StatMech.OSSS.DecisionTree

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]


section Lattice

variable {d : ℕ}


theorem evalR_completeTree_eq_indicator {edge : E → Sym2 (Site d)}
    (hinj : Function.Injective edge) {endU endV : E → Site d}
    (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (B : Set (Site d)) (l : List E) (hl : ∀ e, e ∈ l) (disc₀ : Finset (Site d))
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (hBdisc : ∀ b ∈ B, b ∈ disc₀) :
    (completeTree endU endV o l disc₀).evalR
      = (crossEvent edge o B).indicator (fun _ => (1 : ℝ)) := by
  funext ω
  rw [evalR_completeTree_connected hinj hcoh hadj o B l hl disc₀ hdisc₀ hBdisc ω]
  by_cases hconn : ConnectedToSet d (liftCfg edge ω) o B
  · have hmem : ω ∈ crossEvent edge o B := hconn
    rw [if_pos hconn, Set.indicator_of_mem hmem]
  · have hmem : ω ∉ crossEvent edge o B := hconn
    rw [if_neg hconn, Set.indicator_of_notMem hmem]


theorem covSum_ge_explore {κ : Type*} [Fintype κ] [Nonempty κ]
    {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (l : List E) (hl : ∀ e, e ∈ l)
    (B : Set (Site d)) (disc₀ : κ → Finset (Site d))
    (hdisc₀ : ∀ k, ∀ x ∈ disc₀ k, x ∈ B) (hBdisc : ∀ k, ∀ b ∈ B, b ∈ disc₀ k)
    (R : κ → E → ℝ)
    
    (hRdef : ∀ k e, R k e
      = expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) B then (1 : ℝ) else 0)
        + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) B then (1 : ℝ) else 0))
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D : ℝ) (hDnn : 0 ≤ D) (hD : ∀ e, (∑ k, R k e) ≤ D) :
    (Fintype.card κ : ℝ) * c₀
        * (expect ν ((crossEvent edge o B).indicator (fun _ => (1 : ℝ)))
            * (1 - expect ν ((crossEvent edge o B).indicator (fun _ => (1 : ℝ)))))
      ≤ D * ∑ e, cov ν (coordI e) ((crossEvent edge o B).indicator (fun _ => (1 : ℝ))) := by
  
  set A : Set (ConfigSpace E) := crossEvent edge o B with hA0
  have hAinc : IsIncreasing A := by
    rw [hA0]; unfold crossEvent; exact connectedToSet_increasing edge o B
  
  set T : κ → DecisionTree E := fun k => completeTree endU endV o l (disc₀ k) with hT0
  
  have hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)) := by
    intro k
    rw [hT0, hA0]
    exact evalR_completeTree_eq_indicator hinj hcoh hadj o B l hl (disc₀ k)
      (hdisc₀ k) (hBdisc k)
  
  
  have hR : ∀ k e, reveal ν (T k) e ≤ R k e := by
    intro k e
    rw [hT0, hRdef k e]
    
    unfold completeTree
    exact reveal_exploreTree_le_connected hν hinj hcoh hadj
      (fun disc => decide (o ∈ disc)) B
      (repeatList l (disc₀ k ∪ endpointsFinset endU endV l).card) (disc₀ k)
      (hdisc₀ k) e
  
  exact covSum_ge_of_indicator hν hAinc T hT R hR c₀ hc₀nn hc₀ D hDnn hD


theorem osss_differential_inequality_disch (n : ℕ) (c₀ cR D θ θ' S : ℝ)
    (hD : 0 < D) (hcR : 0 < cR)
    (hcov : (n : ℝ) * c₀ * (θ * (1 - θ)) ≤ D * S)
    (hRussoEq : θ' = cR * S) :
    (n : ℝ) * c₀ * cR / D * (θ * (1 - θ)) ≤ θ' :=
  differential_inequality n c₀ cR D θ θ' S hD hcov (le_of_eq hRussoEq.symm) hcR.le


theorem fk_russo_discharges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℝ} (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 V))) :
    0 < FK.russoPrefactor p ∧
      FK.russoPrefactor p
          * (∑ e ∈ G.edgeFinset, FK.fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
        ≤ deriv (fun p => FK.fkProbOf G p q A) p :=
  ⟨FK.russoPrefactor_pos hp hp1, FK.russo_bound G hp hp1 hq A⟩


theorem osss_subcritical_decay_disch (a b rate : ℝ) (hab : a < b) (hrate : 0 < rate)
    (θn θn' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt θn (θn' x) x)
    (hineq : ∀ x ∈ Icc a b, rate * θn x ≤ θn' x)
    (hθa : 0 ≤ θn a) (hθb : θn b ≤ 1) :
    0 ≤ θn a ∧ θn a ≤ Real.exp (-(rate * (b - a)))
      ∧ Real.exp (-(rate * (b - a))) < 1 :=
  subcritical_decay a b rate hab hrate θn θn' hd hineq hθa hθb


theorem osss_subcritical_decay_box_disch (a b c : ℝ) (n : ℕ) (hab : a < b)
    (hc : 0 < c) (hn : 1 ≤ n) (θn θn' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt θn (θn' x) x)
    (hineq : ∀ x ∈ Icc a b, (c * n) * θn x ≤ θn' x)
    (hθa : 0 ≤ θn a) (hθb : θn b ≤ 1) :
    θn a ≤ Real.exp (-(c * n * (b - a))) :=
  subcritical_decay_box a b c n hab hc hn θn θn' hd hineq hθa hθb

end Lattice
end OSSS
end StatMech
