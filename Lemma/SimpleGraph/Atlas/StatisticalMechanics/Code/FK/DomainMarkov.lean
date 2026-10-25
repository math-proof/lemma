import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
open StatMech StatMech.FK


/--
[agreesOff_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean)
-/
@[path]
private lemma agreesOff_self_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)} :
-- imply
  AgreesOff F ψ ψ := by
-- proof
  apply StatMech.FK.agreesOff_self G F ψ

/--
[agreesOff_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean)
-/
@[path]
private lemma agreesOff_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)}
  {ψ ω : ConfigSpace (Sym2 V)}
-- given
  (h : AgreesOff F ψ ω) :
-- imply
  AgreesOff F ω ψ := by
-- proof
  apply StatMech.FK.agreesOff_symm G h

/--
[agreesOff_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean)
-/
@[path]
private lemma agreesOff_congr_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)}
  {ψ ω : ConfigSpace (Sym2 V)}
-- given
  (h : AgreesOff F ψ ω) :
-- imply
  AgreesOff F ψ = AgreesOff F ω := by
-- proof
  apply StatMech.FK.agreesOff_congr G h

/--
[mem_condFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean)
-/
@[path]
private lemma mem_condFibre_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)}
  {ψ ω : ConfigSpace (Sym2 V)} :
-- imply
  ω ∈ condFibre F ψ ↔ AgreesOff F ψ ω := by
-- proof
  apply StatMech.FK.mem_condFibre G

/--
[self_mem_condFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean)
-/
@[path]
private lemma self_mem_condFibre_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)} :
-- imply
  ψ ∈ condFibre F ψ := by
-- proof
  apply StatMech.FK.self_mem_condFibre G F ψ

/--
[inducedFkZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean)
-/
@[path]
private lemma inducedFkZ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < inducedFkZ G p q F ψ := by
-- proof
  apply StatMech.FK.inducedFkZ_pos G hp hp1 hq F ψ

/--
[inducedFkZ_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean)
-/
@[path]
private lemma inducedFkZ_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  inducedFkZ G p q F ψ ≠ 0 := by
-- proof
  apply StatMech.FK.inducedFkZ_ne_zero G hp hp1 hq F ψ

/--
[inducedFkProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean)
-/
@[path]
private lemma inducedFkProb_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 ≤ inducedFkProb G p q F ψ ω := by
-- proof
  apply StatMech.FK.inducedFkProb_nonneg G hp hp1 hq F ψ ω

/--
[inducedFkProb_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean)
-/
@[path]
private lemma inducedFkProb_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < inducedFkProb G p q F ψ ω := by
-- proof
  apply StatMech.FK.inducedFkProb_pos G hp hp1 hq F ψ ω

/--
[inducedFkProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean)
-/
@[path]
private lemma inducedFkProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∑ ω ∈ condFibre F ψ, inducedFkProb G p q F ψ ω = 1 := by
-- proof
  apply StatMech.FK.inducedFkProb_sum_eq_one G hp hp1 hq F ψ

/--
[condFibre_fkProb_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean)
-/
@[path]
private lemma condFibre_fkProb_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)} :
-- imply
  ∑ ρ ∈ condFibre F ψ, fkProb G p q ρ = inducedFkZ G p q F ψ / fkZ G p q := by
-- proof
  apply StatMech.FK.condFibre_fkProb_sum G F ψ

/--
[condFkProb_eq_inducedFkProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean)
-/
@[path]
private lemma condFkProb_eq_inducedFkProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  condFkProb G p q F ψ ω = inducedFkProb G p q F ψ ω := by
-- proof
  apply StatMech.FK.condFkProb_eq_inducedFkProb G hp hp1 hq F ψ ω

/--
[condFkProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean)
-/
@[path]
private lemma condFkProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∑ ω ∈ condFibre F ψ, condFkProb G p q F ψ ω = 1 := by
-- proof
  apply StatMech.FK.condFkProb_sum_eq_one G hp hp1 hq F ψ

/--
[inducedFkZ_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean)
-/
@[path]
private lemma inducedFkZ_congr_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ ψ' : ConfigSpace (Sym2 V)}
-- given
  (h : AgreesOff F ψ ψ') :
-- imply
  inducedFkZ G p q F ψ = inducedFkZ G p q F ψ' := by
-- proof
  apply StatMech.FK.inducedFkZ_congr G h


-- created on 2026-10-23
