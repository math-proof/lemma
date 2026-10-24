import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.ComparisonHolley
open MeasureTheory StatMech StatMech.FK


/--
[numClusters_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma numClusters_antitone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a a' : ConfigSpace (Sym2 V)}
-- given
  (h : a ≤ a') :
-- imply
  numClusters G a' ≤ numClusters G a := by
-- proof
  apply StatMech.FK.numClusters_antitone G h

/--
[numClusters_setOpen_succ_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma numClusters_setOpen_succ_of_closed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b : ConfigSpace (Sym2 V)}
  {e : Sym2 V}
-- given
  (hclosed : b e = false) :
-- imply
  numClusters G b ≤ numClusters G (setOpen e b) + 1 := by
-- proof
  apply StatMech.FK.numClusters_setOpen_succ_of_closed G hclosed

/--
[openCount_setOpen_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma openCount_setOpen_of_closed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)}
  {e : Sym2 V}
-- given
  (he : e ∈ G.edgeFinset)
  (hclosed : ω e = false) :
-- imply
  chOpenCount G (setOpen e ω) = chOpenCount G ω + 1 := by
-- proof
  apply StatMech.FK.openCount_setOpen_of_closed G he hclosed

/--
[openSub_eq_of_diffSet_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma openSub_eq_of_diffSet_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b c : ConfigSpace (Sym2 V)}
-- given
  (hle : b ≤ c)
  (hempty : diffSet G b c = ∅) :
-- imply
  openSub G b = openSub G c := by
-- proof
  apply StatMech.FK.openSub_eq_of_diffSet_empty G hle hempty

/--
[setOpen_le_of_mem_diffSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma setOpen_le_of_mem_diffSet_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b c : ConfigSpace (Sym2 V)}
  {e : Sym2 V}
-- given
  (hle : b ≤ c)
  (hmem : e ∈ diffSet G b c) :
-- imply
  setOpen e b ≤ c := by
-- proof
  apply StatMech.FK.setOpen_le_of_mem_diffSet G hle hmem

/--
[diffSet_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma diffSet_setOpen_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b c : ConfigSpace (Sym2 V)}
  {e : Sym2 V}
-- given
  (hmem : e ∈ diffSet G b c) :
-- imply
  diffSet G (setOpen e b) c = (diffSet G b c).erase e := by
-- proof
  apply StatMech.FK.diffSet_setOpen G hmem

/--
[numClusters_add_openCount_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma numClusters_add_openCount_mono_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∀ (n : ℕ) (b c : ConfigSpace (Sym2 V)), b ≤ c → (diffSet G b c).card = n → numClusters G b + chOpenCount G b ≤ numClusters G c + chOpenCount G c := by
-- proof
  apply StatMech.FK.numClusters_add_openCount_mono G

/--
[edgeProduct_modular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma edgeProduct_modular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {a b : ConfigSpace (Sym2 V)} :
-- imply
  edgeProduct G p a * edgeProduct G p b = edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
-- proof
  apply StatMech.FK.edgeProduct_modular G p a b

/--
[fkWeight_cross_bernoulli_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma fkWeight_cross_bernoulli_upper_eq
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
  fkWeight G p q a * edgeProduct G p b ≤ fkWeight G p q (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
-- proof
  apply StatMech.FK.fkWeight_cross_bernoulli_upper G hp hp1 hq a b

/--
[reducedDensity_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma reducedDensity_mem_Ioo_eq
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
  0 < reducedDensity p q ∧ reducedDensity p q < 1 := by
-- proof
  apply StatMech.FK.reducedDensity_mem_Ioo G hp hp1 hq

/--
[reducedDensity_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma reducedDensity_key_eq
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
  q * reducedDensity p q * (1 - p) = (1 - reducedDensity p q) * p := by
-- proof
  apply StatMech.FK.reducedDensity_key G hp hp1 hq

/--
[edgeFactor_bernoulli_lower_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma edgeFactor_bernoulli_lower_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {α β : Bool}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (if α then reducedDensity p q else 1 - reducedDensity p q) * (if β then p else 1 - p) * (if (!β && α) then q else 1) = (if (α && β) then reducedDensity p q else 1 - reducedDensity p q) * (if (α || β) then p else 1 - p) := by
-- proof
  apply StatMech.FK.edgeFactor_bernoulli_lower_eq G hp hp1 hq α β

/--
[edgeProduct_bernoulli_lower_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma edgeProduct_bernoulli_lower_eq_eq
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
  edgeProduct G (reducedDensity p q) a * edgeProduct G p b * ∏ e ∈ G.edgeFinset, (if (!(b e) && a e) = true then q else (1 : ℝ)) = edgeProduct G (reducedDensity p q) (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
-- proof
  apply StatMech.FK.edgeProduct_bernoulli_lower_eq G hp hp1 hq a b

/--
[qFactor_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma qFactor_eq_pow_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℝ}
  {a b : ConfigSpace (Sym2 V)} :
-- imply
  ∏ e ∈ G.edgeFinset, (if (!(b e) && a e) = true then q else (1 : ℝ)) = q ^ (G.edgeFinset.filter (fun e => (!(b e) && a e) = true)).card := by
-- proof
  apply StatMech.FK.qFactor_eq_pow G q a b

/--
[openCount_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma openCount_sup_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : ConfigSpace (Sym2 V)} :
-- imply
  chOpenCount G (a ⊔ b) = chOpenCount G b + (G.edgeFinset.filter (fun e => (!(b e) && a e) = true)).card := by
-- proof
  apply StatMech.FK.openCount_sup G a b

/--
[numClusters_le_sup_add_opened](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma numClusters_le_sup_add_opened_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : ConfigSpace (Sym2 V)} :
-- imply
  numClusters G b ≤ numClusters G (a ⊔ b) + (G.edgeFinset.filter (fun e => (!(b e) && a e) = true)).card := by
-- proof
  apply StatMech.FK.numClusters_le_sup_add_opened G a b

/--
[edgeProduct_cross_bernoulli_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma edgeProduct_cross_bernoulli_lower_eq
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
  edgeProduct G (reducedDensity p q) a * fkWeight G p q b ≤ edgeProduct G (reducedDensity p q) (a ⊓ b) * fkWeight G p q (a ⊔ b) := by
-- proof
  apply StatMech.FK.edgeProduct_cross_bernoulli_lower G hp hp1 hq a b

/--
[fkProb_cross_bernoulli_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma fkProb_cross_bernoulli_upper_eq
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
  fkProb G p q a * fkProb G p 1 b ≤ fkProb G p q (a ⊓ b) * fkProb G p 1 (a ⊔ b) := by
-- proof
  apply StatMech.FK.fkProb_cross_bernoulli_upper G hp hp1 hq a b

/--
[fkProb_cross_bernoulli_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma fkProb_cross_bernoulli_lower_eq
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
  fkProb G (reducedDensity p q) 1 a * fkProb G p q b ≤ fkProb G (reducedDensity p q) 1 (a ⊓ b) * fkProb G p q (a ⊔ b) := by
-- proof
  apply StatMech.FK.fkProb_cross_bernoulli_lower G hp hp1 hq a b

/--
[fk_monotone_in_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma fk_monotone_in_p_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p₁ p₂ q : ℝ}
-- given
  (hp₁ : 0 < p₁)
  (hp₁' : p₁ < 1)
  (hp₂ : 0 < p₂)
  (hp₂' : p₂ < 1)
  (hle : p₁ ≤ p₂)
  (hq : 1 ≤ q) :
-- imply
  measOfMass (fkProb G p₁ q) ≼ measOfMass (fkProb G p₂ q) := by
-- proof
  apply StatMech.FK.fk_monotone_in_p G hp₁ hp₁' hp₂ hp₂' hle hq

/--
[fk_le_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma fk_le_bernoulli_eq
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
  measOfMass (fkProb G p q) ≼ measOfMass (fkProb G p 1) := by
-- proof
  apply StatMech.FK.fk_le_bernoulli G hp hp1 hq

/--
[bernoulli_reduced_le_fk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma bernoulli_reduced_le_fk_eq
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
  measOfMass (fkProb G (reducedDensity p q) 1) ≼ measOfMass (fkProb G p q) := by
-- proof
  apply StatMech.FK.bernoulli_reduced_le_fk G hp hp1 hq

/--
[fk_bernoulli_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean)
-/
@[path]
private lemma fk_bernoulli_sandwich_eq
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
  measOfMass (fkProb G (reducedDensity p q) 1) ≼ measOfMass (fkProb G p q) ∧ measOfMass (fkProb G p q) ≼ measOfMass (fkProb G p 1) := by
-- proof
  apply StatMech.FK.fk_bernoulli_sandwich G hp hp1 hq


-- created on 2026-10-23
