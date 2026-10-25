import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.CircuitLowerBound.Part6
open StatMech StatMech.FK


/--
[fkWeight_setClosed_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma fkWeight_setClosed_ge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q * (fkWeight G p q (setOpen e ω) + fkWeight G p q (setClosed e ω)) ≤ fkWeight G p q (setClosed e ω) := by
-- proof
  apply StatMech.FK.fkWeight_setClosed_ge G hp hp1 hq e ω

/--
[closeAllOn_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma closeAllOn_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {γ : Finset (Sym2 V)}
  {e : Sym2 V}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (he : e ∈ γ) :
-- imply
  closeAllOn γ ψ e = false := by
-- proof
  apply StatMech.FK.closeAllOn_of_mem G he ψ

/--
[closeAllOn_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma closeAllOn_of_not_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {γ : Finset (Sym2 V)}
  {e : Sym2 V}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ γ) :
-- imply
  closeAllOn γ ψ e = ψ e := by
-- proof
  apply StatMech.FK.closeAllOn_of_not_mem G he ψ

/--
[closeAllOn_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma closeAllOn_setClosed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 V}
  {γ : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ γ) :
-- imply
  closeAllOn γ (setClosed e ψ) = setClosed e (closeAllOn γ ψ) := by
-- proof
  apply StatMech.FK.closeAllOn_setClosed G he ψ

/--
[closeAllOn_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma closeAllOn_setOpen_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 V}
  {γ : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ γ) :
-- imply
  closeAllOn γ (setOpen e ψ) = setOpen e (closeAllOn γ ψ) := by
-- proof
  apply StatMech.FK.closeAllOn_setOpen G he ψ

/--
[agreeWeightSum_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma agreeWeightSum_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {γ : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < agreeWeightSum G p q γ ψ := by
-- proof
  apply StatMech.FK.agreeWeightSum_pos G hp hp1 hq γ ψ

/--
[agreeWeightSum_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma agreeWeightSum_insert_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {γ : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ γ) :
-- imply
  agreeWeightSum G p q (insert e γ) ψ = agreeWeightSum G p q γ (setClosed e ψ) + agreeWeightSum G p q γ (setOpen e ψ) := by
-- proof
  apply StatMech.FK.agreeWeightSum_insert G p q he ψ

/--
[agreeWeightSum_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma agreeWeightSum_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 V)} :
-- imply
  agreeWeightSum G p q ∅ ψ = fkWeight G p q ψ := by
-- proof
  apply StatMech.FK.agreeWeightSum_empty G p q ψ

/--
[cFE_pow_mul_agreeWeightSum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma cFE_pow_mul_agreeWeightSum_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {γ : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ^ γ.card * agreeWeightSum G p q γ ψ ≤ fkWeight G p q (closeAllOn γ ψ) := by
-- proof
  apply StatMech.FK.cFE_pow_mul_agreeWeightSum_le G hp hp1 hq γ ψ

/--
[cFE_pow_le_condClosedOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma cFE_pow_le_condClosedOn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {γ : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ^ γ.card ≤ fkWeight G p q (closeAllOn γ ψ) / agreeWeightSum G p q γ ψ := by
-- proof
  apply StatMech.FK.cFE_pow_le_condClosedOn G hp hp1 hq γ ψ

/--
[closedMass_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma closedMass_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  closedMass G p q ∅ = 1 := by
-- proof
  apply StatMech.FK.closedMass_empty G hp hp1 hq

/--
[closedMass_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma closedMass_reindex_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {γ : Finset (Sym2 V)}
-- given
  (he : e ∉ γ) :
-- imply
  closedMass G p q γ = ∑ ψ ∈ cfib e γ, (fkProb G p q (setOpen e ψ) + fkProb G p q (setClosed e ψ)) := by
-- proof
  apply StatMech.FK.closedMass_reindex G e he

/--
[closedMass_insert_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma closedMass_insert_reindex_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {γ : Finset (Sym2 V)}
-- given
  (he : e ∉ γ) :
-- imply
  closedMass G p q (insert e γ) = ∑ ψ ∈ cfib e γ, fkProb G p q (setClosed e ψ) := by
-- proof
  apply StatMech.FK.closedMass_insert_reindex G e he

/--
[cFE_mul_closedMass_le_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma cFE_mul_closedMass_le_insert_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {γ : Finset (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (he : e ∉ γ) :
-- imply
  cFE p q * closedMass G p q γ ≤ closedMass G p q (insert e γ) := by
-- proof
  apply StatMech.FK.cFE_mul_closedMass_le_insert G hp hp1 hq e he

/--
[cFE_pow_le_closedMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma cFE_pow_le_closedMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {γ : Finset (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ^ γ.card ≤ closedMass G p q γ := by
-- proof
  apply StatMech.FK.cFE_pow_le_closedMass G hp hp1 hq γ

/--
[closedMass_eq_indicator_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma closedMass_eq_indicator_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {γ : Finset (Sym2 V)} :
-- imply
  closedMass G p q γ = ∑ ω, (closedEvent γ).indicator (fun _ => (1 : ℝ)) ω * fkProb G p q ω := by
-- proof
  apply StatMech.FK.closedMass_eq_indicator_sum G p q γ

/--
[cFE_pow_le_closedEventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean)
-/
@[path]
private lemma cFE_pow_le_closedEventMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {γ : Finset (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ^ γ.card ≤ ∑ ω, (closedEvent γ).indicator (fun _ => (1 : ℝ)) ω * fkProb G p q ω := by
-- proof
  apply StatMech.FK.cFE_pow_le_closedEventMass G hp hp1 hq γ


-- created on 2026-10-23
