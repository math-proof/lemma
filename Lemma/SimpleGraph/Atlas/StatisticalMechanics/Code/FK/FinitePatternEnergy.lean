import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
open MeasureTheory Finset StatMech StatMech.FK


/--
[numClustersBC_setOpen_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma numClustersBC_setOpen_bounds_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {e : Sym2 V}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  numClustersBC G C (setOpen e omega) ≤ numClustersBC G C (setClosed e omega) ∧ numClustersBC G C (setClosed e omega) ≤ numClustersBC G C (setOpen e omega) + 1 := by
-- proof
  apply StatMech.FK.numClustersBC_setOpen_bounds G C e omega

/--
[bcWeight_lo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma bcWeight_lo_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (he : e ∈ G.edgeFinset) :
-- imply
  (1 - p) * bcWeight G C p q (setOpen e omega) ≤ p * bcWeight G C p q (setClosed e omega) := by
-- proof
  apply StatMech.FK.bcWeight_lo G C hp hp1 hq he omega

/--
[bcWeight_hi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma bcWeight_hi_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (he : e ∈ G.edgeFinset) :
-- imply
  p * bcWeight G C p q (setClosed e omega) ≤ q * (1 - p) * bcWeight G C p q (setOpen e omega) := by
-- proof
  apply StatMech.FK.bcWeight_hi G C hp hp1 hq he omega

/--
[bcWeight_setOpen_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma bcWeight_setOpen_ge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q * (bcWeight G C p q (setOpen e omega) + bcWeight G C p q (setClosed e omega)) ≤ bcWeight G C p q (setOpen e omega) := by
-- proof
  apply StatMech.FK.bcWeight_setOpen_ge G C hp hp1 hq e omega

/--
[bcWeight_setClosed_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma bcWeight_setClosed_ge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q * (bcWeight G C p q (setOpen e omega) + bcWeight G C p q (setClosed e omega)) ≤ bcWeight G C p q (setClosed e omega) := by
-- proof
  apply StatMech.FK.bcWeight_setClosed_ge G C hp hp1 hq e omega

/--
[fkWeight_setOpen_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma fkWeight_setOpen_ge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {p q : ℝ}
  {e : Sym2 V}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q * (fkWeight G p q (setOpen e omega) + fkWeight G p q (setClosed e omega)) ≤ fkWeight G p q (setOpen e omega) := by
-- proof
  apply StatMech.FK.fkWeight_setOpen_ge G C hp hp1 hq e omega

/--
[setPattern_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma setPattern_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {e : Sym2 V}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (he : e ∈ I) :
-- imply
  setPattern I eta psi e = eta ⟨e, he⟩ := by
-- proof
  apply StatMech.FK.setPattern_of_mem G C eta he psi

/--
[setPattern_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma setPattern_of_not_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {e : Sym2 V}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ I) :
-- imply
  setPattern I eta psi e = psi e := by
-- proof
  apply StatMech.FK.setPattern_of_not_mem G C eta he psi

/--
[setPattern_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma setPattern_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {eta : ConfigSpace ↥(∅ : Finset (Sym2 V))}
  {psi : ConfigSpace (Sym2 V)} :
-- imply
  setPattern ∅ eta psi = psi := by
-- proof
  apply StatMech.FK.setPattern_empty G C eta psi

/--
[setPattern_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma setPattern_setClosed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {e : Sym2 V}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ I) :
-- imply
  setPattern I eta (setClosed e psi) = setClosed e (setPattern I eta psi) := by
-- proof
  apply StatMech.FK.setPattern_setClosed G C eta he psi

/--
[setPattern_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma setPattern_setOpen_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {e : Sym2 V}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ I) :
-- imply
  setPattern I eta (setOpen e psi) = setOpen e (setPattern I eta psi) := by
-- proof
  apply StatMech.FK.setPattern_setOpen G C eta he psi

/--
[inducedBcZ_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma inducedBcZ_insert_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {I : Finset (Sym2 V)}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ I) :
-- imply
  inducedBcZ G C p q (insert e I) psi = inducedBcZ G C p q I (setClosed e psi) + inducedBcZ G C p q I (setOpen e psi) := by
-- proof
  apply StatMech.FK.inducedBcZ_insert G C C p q he psi

/--
[inducedBcZ_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma inducedBcZ_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {psi : ConfigSpace (Sym2 V)} :
-- imply
  inducedBcZ G C p q ∅ psi = bcWeight G C p q psi := by
-- proof
  apply StatMech.FK.inducedBcZ_empty G C C p q psi

/--
[cFE_pow_mul_inducedBcZ_le_setPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma cFE_pow_mul_inducedBcZ_le_setPattern_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ^ I.card * inducedBcZ G C p q I psi ≤ bcWeight G C p q (setPattern I eta psi) := by
-- proof
  apply StatMech.FK.cFE_pow_mul_inducedBcZ_le_setPattern G C C hp hp1 hq I eta psi

/--
[cFE_pow_mul_agreeWeightSum_le_setPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma cFE_pow_mul_agreeWeightSum_le_setPattern_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {p q : ℝ}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ^ I.card * agreeWeightSum G p q I psi ≤ fkWeight G p q (setPattern I eta psi) := by
-- proof
  apply StatMech.FK.cFE_pow_mul_agreeWeightSum_le_setPattern G C C hp hp1 hq I eta psi

/--
[setPattern_mem_patternEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma setPattern_mem_patternEvent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {psi : ConfigSpace (Sym2 V)} :
-- imply
  setPattern I eta psi ∈ patternEvent I eta := by
-- proof
  apply StatMech.FK.setPattern_mem_patternEvent G C C I eta psi

/--
[agreesOff_setPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma agreesOff_setPattern_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {psi : ConfigSpace (Sym2 V)} :
-- imply
  AgreesOff I psi (setPattern I eta psi) := by
-- proof
  apply StatMech.FK.agreesOff_setPattern G C C I eta psi

/--
[eq_setPattern_of_agreesOff_of_mem_pattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma eq_setPattern_of_agreesOff_of_mem_pattern_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {psi omega : ConfigSpace (Sym2 V)}
-- given
  (hoff : AgreesOff I psi omega)
  (hpat : omega ∈ patternEvent I eta) :
-- imply
  omega = setPattern I eta psi := by
-- proof
  apply StatMech.FK.eq_setPattern_of_agreesOff_of_mem_pattern G C C hoff hpat

/--
[setPattern_eq_self_of_mem_pattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma setPattern_eq_self_of_mem_pattern_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hpat : omega ∈ patternEvent I eta) :
-- imply
  setPattern I eta omega = omega := by
-- proof
  apply StatMech.FK.setPattern_eq_self_of_mem_pattern G C C hpat

/--
[dependsOnOutside_preimage_setPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma dependsOnOutside_preimage_setPattern_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {A : Set (ConfigSpace (Sym2 V))} :
-- imply
  DependsOnOutside I (setPattern I eta ⁻¹' A) := by
-- proof
  apply StatMech.FK.dependsOnOutside_preimage_setPattern G C C I eta A

/--
[cFE_pow_le_condBcProb_pattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma cFE_pow_le_condBcProb_pattern_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ^ I.card ≤ ∑ omega, (patternEvent I eta).indicator (fun _ => (1 : ℝ)) omega * condBcProb G C p q I psi omega := by
-- proof
  apply StatMech.FK.cFE_pow_le_condBcProb_pattern G C C C hp hp1 hq I eta psi

/--
[cFE_pow_mul_condFibreMass_le_pattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma cFE_pow_mul_condFibreMass_le_pattern_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {p q : ℝ}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ^ I.card * (∑ omega ∈ condFibre I psi, fkProb G p q omega) ≤ fkProb G p q (setPattern I eta psi) := by
-- proof
  apply StatMech.FK.cFE_pow_mul_condFibreMass_le_pattern G C C hp hp1 hq I eta psi

/--
[cFE_pow_le_condFkProb_pattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma cFE_pow_le_condFkProb_pattern_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {p q : ℝ}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ^ I.card ≤ ∑ omega ∈ condFibre I psi, (patternEvent I eta).indicator (fun _ => (1 : ℝ)) omega * condFkProb G p q I psi omega := by
-- proof
  apply StatMech.FK.cFE_pow_le_condFkProb_pattern G C C hp hp1 hq I eta psi

/--
[fkProb_eq_fibreMass_mul_condFkProb_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma fkProb_eq_fibreMass_mul_condFkProb_general_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {p q : ℝ}
  {I : Finset (Sym2 V)}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  fkProb G p q omega = (∑ rho ∈ condFibre I omega, fkProb G p q rho) * condFkProb G p q I omega omega := by
-- proof
  apply StatMech.FK.fkProb_eq_fibreMass_mul_condFkProb_general G C C hp hp1 hq I omega

/--
[fkProb_fibre_decompose_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma fkProb_fibre_decompose_general_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {p q : ℝ}
  {I : Finset (Sym2 V)}
  {B : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ omega, B.indicator (fun _ => (1 : ℝ)) omega * fkProb G p q omega) = ∑ psi ∈ fibreReps I, (∑ sigma ∈ condFibre I psi, fkProb G p q sigma) * (∑ rho ∈ condFibre I psi, B.indicator (fun _ => (1 : ℝ)) rho * condFkProb G p q I psi rho) := by
-- proof
  apply StatMech.FK.fkProb_fibre_decompose_general G C C hp hp1 hq I B

/--
[condFkProb_sum_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma condFkProb_sum_outside_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {p q : ℝ}
  {I : Finset (Sym2 V)}
  {B : Set (ConfigSpace (Sym2 V))}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hB : DependsOnOutside I B) :
-- imply
  (∑ rho ∈ condFibre I psi, B.indicator (fun _ => (1 : ℝ)) rho * condFkProb G p q I psi rho) = B.indicator (fun _ => (1 : ℝ)) psi := by
-- proof
  apply StatMech.FK.condFkProb_sum_outside G C C hp hp1 hq hB psi

/--
[condFkProb_cross_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma condFkProb_cross_outside_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {p q : ℝ}
  {I : Finset (Sym2 V)}
  {A B : Set (ConfigSpace (Sym2 V))}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (hB : DependsOnOutside I B) :
-- imply
  (∑ rho ∈ condFibre I psi, (A ∩ B).indicator (fun _ => (1 : ℝ)) rho * condFkProb G p q I psi rho) = B.indicator (fun _ => (1 : ℝ)) psi * (∑ rho ∈ condFibre I psi, A.indicator (fun _ => (1 : ℝ)) rho * condFkProb G p q I psi rho) := by
-- proof
  apply StatMech.FK.condFkProb_cross_outside G C C hB psi

/--
[cFE_pow_mul_event_le_pattern_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma cFE_pow_mul_event_le_pattern_inter_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {p q : ℝ}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {B : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hB : DependsOnOutside I B) :
-- imply
  cFE p q ^ I.card * (∑ omega, B.indicator (fun _ => (1 : ℝ)) omega * fkProb G p q omega) ≤ ∑ omega, (patternEvent I eta ∩ B).indicator (fun _ => (1 : ℝ)) omega * fkProb G p q omega := by
-- proof
  apply StatMech.FK.cFE_pow_mul_event_le_pattern_inter G C C hp hp1 hq I eta B hB

/--
[cFE_pow_mul_bcEvent_le_pattern_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma cFE_pow_mul_bcEvent_le_pattern_inter_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {B : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hB : DependsOnOutside I B) :
-- imply
  cFE p q ^ I.card * (∑ omega, B.indicator (fun _ => (1 : ℝ)) omega * bcProb G C p q omega) ≤ ∑ omega, (patternEvent I eta ∩ B).indicator (fun _ => (1 : ℝ)) omega * bcProb G C p q omega := by
-- proof
  apply StatMech.FK.cFE_pow_mul_bcEvent_le_pattern_inter G C C C hp hp1 hq I eta B hB

/--
[cFE_pow_mul_bcPreimage_le_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean)
-/
@[path]
private lemma cFE_pow_mul_bcPreimage_le_event_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C}
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ^ I.card * (∑ omega, (setPattern I eta ⁻¹' A).indicator (fun _ => (1 : ℝ)) omega * bcProb G C p q omega) ≤ ∑ omega, A.indicator (fun _ => (1 : ℝ)) omega * bcProb G C p q omega := by
-- proof
  apply StatMech.FK.cFE_pow_mul_bcPreimage_le_event G C C C hp hp1 hq I eta A


-- created on 2026-10-23
