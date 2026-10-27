import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
open SimpleGraph StatMech StatMech.FK


/--
[projOff_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean)
-/
@[path]
private lemma projOff_idem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)} :
-- imply
  projOff F (projOff F ψ) = projOff F ψ := by
-- proof
  apply StatMech.FK.projOff_idem G C F ψ

/--
[agreesOff_projOff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean)
-/
@[path]
private lemma agreesOff_projOff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)} :
-- imply
  AgreesOff F (projOff F ψ) ψ := by
-- proof
  apply StatMech.FK.agreesOff_projOff G C F ψ

/--
[projOff_eq_of_agreesOff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean)
-/
@[path]
private lemma projOff_eq_of_agreesOff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {F : Finset (Sym2 V)}
  {ψ ρ : ConfigSpace (Sym2 V)}
-- given
  (h : AgreesOff F ψ ρ) :
-- imply
  projOff F ρ = projOff F ψ := by
-- proof
  apply StatMech.FK.projOff_eq_of_agreesOff G C h

/--
[filter_projOff_eq_condFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean)
-/
@[path]
private lemma filter_projOff_eq_condFibre_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (hψ : projOff F ψ = ψ) :
-- imply
  Finset.univ.filter (fun ρ => projOff F ρ = ψ) = condFibre F ψ := by
-- proof
  apply StatMech.FK.filter_projOff_eq_condFibre G C F ψ hψ

/--
[condFibre_congr_dom'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean)
-/
@[path]
private lemma condFibre_congr_dom'_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {F : Finset (Sym2 V)}
  {ψ ψ' : ConfigSpace (Sym2 V)}
-- given
  (h : AgreesOff F ψ ψ') :
-- imply
  condFibre F ψ = condFibre F ψ' := by
-- proof
  apply StatMech.FK.condFibre_congr_dom' G C h

/--
[condBcProb_congr_dom'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean)
-/
@[path]
private lemma condBcProb_congr_dom'_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ ψ' ω : ConfigSpace (Sym2 V)}
-- given
  (h : AgreesOff F ψ ψ') :
-- imply
  condBcProb G C p q F ψ ω = condBcProb G C p q F ψ' ω := by
-- proof
  apply StatMech.FK.condBcProb_congr_dom' G C p q F ψ ψ' ω h

/--
[bcProb_fibre_decompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean)
-/
@[path]
private lemma bcProb_fibre_decompose_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {B : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ) = ∑ ψ ∈ fibreReps F, (∑ σ ∈ condFibre F ψ, bcProb G C p q σ) * (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ) := by
-- proof
  apply StatMech.FK.bcProb_fibre_decompose G C hp hp1 hq F B

/--
[indicator_const_on_fibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean)
-/
@[path]
private lemma indicator_const_on_fibre_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {F : Finset (Sym2 V)}
  {B : Set (ConfigSpace (Sym2 V))}
  {ψ ρ : ConfigSpace (Sym2 V)}
-- given
  (hB : DependsOnOutside F B)
  (hρ : AgreesOff F ψ ρ) :
-- imply
  B.indicator (fun _ => (1:ℝ)) ρ = B.indicator (fun _ => (1:ℝ)) ψ := by
-- proof
  apply StatMech.FK.indicator_const_on_fibre G C hB hρ

/--
[condBcProb_sum_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean)
-/
@[path]
private lemma condBcProb_sum_outside_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {B : Set (ConfigSpace (Sym2 V))}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hB : DependsOnOutside F B)
  (hψ : projOff F ψ = ψ) :
-- imply
  (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ) = B.indicator (fun _ => (1:ℝ)) ψ := by
-- proof
  apply StatMech.FK.condBcProb_sum_outside G C hp hp1 hq hB hψ

/--
[condBcProb_cross_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean)
-/
@[path]
private lemma condBcProb_cross_outside_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {A B : Set (ConfigSpace (Sym2 V))}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (hB : DependsOnOutside F B) :
-- imply
  (∑ ρ, (A ∩ B).indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ) = B.indicator (fun _ => (1:ℝ)) ψ * (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ) := by
-- proof
  apply StatMech.FK.condBcProb_cross_outside G C hB

/--
[bcProb_disjoint_product_dom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean)
-/
@[path]
private lemma bcProb_disjoint_product_dom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {A B : Set (ConfigSpace (Sym2 V))}
  {α : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hB : DependsOnOutside F B)
  (hα : 0 ≤ α)
  (hres : ∀ ψ ∈ fibreReps F, (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ) ≤ α) :
-- imply
  (∑ ρ, (A ∩ B).indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ) ≤ α * (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ) := by
-- proof
  apply StatMech.FK.bcProb_disjoint_product_dom G C hp hp1 hq hB hα hres

/--
[bcProb_disjoint_product_lower_of_conditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean)
-/
@[path]
private lemma bcProb_disjoint_product_lower_of_conditional_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {A B : Set (ConfigSpace (Sym2 V))}
  {α : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hB : DependsOnOutside F B)
  (hres : ∀ ψ ∈ fibreReps F, α ≤ ∑ ρ, A.indicator (fun _ => (1 : ℝ)) ρ * condBcProb G C p q F ψ ρ) :
-- imply
  α * (∑ ρ, B.indicator (fun _ => (1 : ℝ)) ρ * bcProb G C p q ρ) ≤ ∑ ρ, (A ∩ B).indicator (fun _ => (1 : ℝ)) ρ * bcProb G C p q ρ := by
-- proof
  apply StatMech.FK.bcProb_disjoint_product_lower_of_conditional G C hp hp1 hq hB hres

/--
[perFibre_dom_of_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean)
-/
@[path]
private lemma perFibre_dom_of_wired_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {A : Set (ConfigSpace (Sym2 V))}
  {α : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hCC' : C ≤ C')
  (hA : IsIncreasing A)
  (hres' : ∀ ψ ∈ fibreReps F, (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C' p q F ψ ρ) ≤ α) :
-- imply
  ∀ ψ ∈ fibreReps F, (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ) ≤ α := by
-- proof
  apply StatMech.FK.perFibre_dom_of_wired G C hp hp1 hq C' hCC' hA hres'

/--
[bcProb_disjoint_product_dom_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean)
-/
@[path]
private lemma bcProb_disjoint_product_dom_wired_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {A B : Set (ConfigSpace (Sym2 V))}
  {α : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hCC' : C ≤ C')
  (hA : IsIncreasing A)
  (hB : DependsOnOutside F B)
  (hα : 0 ≤ α)
  (hres' : ∀ ψ ∈ fibreReps F, (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C' p q F ψ ρ) ≤ α) :
-- imply
  (∑ ρ, (A ∩ B).indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ) ≤ α * (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ) := by
-- proof
  apply StatMech.FK.bcProb_disjoint_product_dom_wired G C hp hp1 hq C' hCC' hA hB hα hres'


-- created on 2026-10-23
