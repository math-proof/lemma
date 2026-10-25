import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PositiveAssociation
open StatMech StatMech.FK


/--
[fkWeightNN_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PositiveAssociation.lean)
-/
@[path]
private lemma fkWeightNN_coe_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (fkWeightNN G p q hp hp1 hq ω : ℝ) = fkWeight G p q ω := by
-- proof
  apply StatMech.FK.fkWeightNN_coe G hp hp1 hq ω

/--
[fk_fkgCondition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PositiveAssociation.lean)
-/
@[path]
private lemma fk_fkgCondition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Probability.FKGCondition (fkWeightNN G p q hp hp1 (lt_of_lt_of_le zero_lt_one hq)) := by
-- proof
  apply StatMech.FK.fk_fkgCondition G hp hp1 hq

/--
[fkProb_fkgLattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PositiveAssociation.lean)
-/
@[path]
private lemma fkProb_fkgLattice_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  fkProb G p q a * fkProb G p q b ≤ fkProb G p q (a ⊓ b) * fkProb G p q (a ⊔ b) := by
-- proof
  apply StatMech.FK.fkProb_fkgLattice G hp hp1 hq a b

/--
[fk_positively_associated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PositiveAssociation.lean)
-/
@[path]
private lemma fk_positively_associated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {f g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  (∑ ω, fkProb G p q ω * f ω) * (∑ ω, fkProb G p q ω * g ω) ≤ ∑ ω, fkProb G p q ω * (f ω * g ω) := by
-- proof
  apply StatMech.FK.fk_positively_associated G hp hp1 hq hf hg

/--
[fk_positively_associated_events](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PositiveAssociation.lean)
-/
@[path]
private lemma fk_positively_associated_events_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A B : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  (∑ ω, fkProb G p q ω * A.indicator (fun _ => (1 : ℝ)) ω) * (∑ ω, fkProb G p q ω * B.indicator (fun _ => (1 : ℝ)) ω) ≤ ∑ ω, fkProb G p q ω * (A ∩ B).indicator (fun _ => (1 : ℝ)) ω := by
-- proof
  apply StatMech.FK.fk_positively_associated_events G hp hp1 hq hA hB


-- created on 2026-10-23
