import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
open SimpleGraph StatMech StatMech.FK


/--
[agreesOff_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean)
-/
@[path]
private lemma agreesOff_inf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)}
  {ψ a b : ConfigSpace (Sym2 V)}
-- given
  (ha : AgreesOff F ψ a)
  (hb : AgreesOff F ψ b) :
-- imply
  AgreesOff F ψ (a ⊓ b) := by
-- proof
  apply StatMech.FK.agreesOff_inf G ha hb

/--
[agreesOff_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean)
-/
@[path]
private lemma agreesOff_sup_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)}
  {ψ a b : ConfigSpace (Sym2 V)}
-- given
  (ha : AgreesOff F ψ a)
  (hb : AgreesOff F ψ b) :
-- imply
  AgreesOff F ψ (a ⊔ b) := by
-- proof
  apply StatMech.FK.agreesOff_sup G ha hb

/--
[condFibre_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean)
-/
@[path]
private lemma condFibre_inf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)}
  {ψ a b : ConfigSpace (Sym2 V)}
-- given
  (ha : a ∈ condFibre F ψ)
  (hb : b ∈ condFibre F ψ) :
-- imply
  a ⊓ b ∈ condFibre F ψ := by
-- proof
  apply StatMech.FK.condFibre_inf G ha hb

/--
[condFibre_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean)
-/
@[path]
private lemma condFibre_sup_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)}
  {ψ a b : ConfigSpace (Sym2 V)}
-- given
  (ha : a ∈ condFibre F ψ)
  (hb : b ∈ condFibre F ψ) :
-- imply
  a ⊔ b ∈ condFibre F ψ := by
-- proof
  apply StatMech.FK.condFibre_sup G ha hb

/--
[inducedBcZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean)
-/
@[path]
private lemma inducedBcZ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < inducedBcZ G C p q F ψ := by
-- proof
  apply StatMech.FK.inducedBcZ_pos G C hp hp1 hq F ψ

/--
[inducedBcZ_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean)
-/
@[path]
private lemma inducedBcZ_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  inducedBcZ G C p q F ψ ≠ 0 := by
-- proof
  apply StatMech.FK.inducedBcZ_ne_zero G C hp hp1 hq F ψ

/--
[condBcProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean)
-/
@[path]
private lemma condBcProb_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (0 : ConfigSpace (Sym2 V) → ℝ) ≤ condBcProb G C p q F ψ := by
-- proof
  apply StatMech.FK.condBcProb_nonneg G C hp hp1 hq F ψ

/--
[condBcProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean)
-/
@[path]
private lemma condBcProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∑ ω : ConfigSpace (Sym2 V), condBcProb G C p q F ψ ω = 1 := by
-- proof
  apply StatMech.FK.condBcProb_sum_eq_one G C hp hp1 hq F ψ

/--
[condBcProb_eq_div_bcProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean)
-/
@[path]
private lemma condBcProb_eq_div_bcProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hω : AgreesOff F ψ ω) :
-- imply
  condBcProb G C p q F ψ ω = bcProb G C p q ω / (∑ ρ ∈ condFibre F ψ, bcProb G C p q ρ) := by
-- proof
  apply StatMech.FK.condBcProb_eq_div_bcProb G C hp hp1 hq F ψ ω hω

/--
[condBcProb_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean)
-/
@[path]
private lemma condBcProb_cross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ a b : ConfigSpace (Sym2 V)}
-- given
  (hCC' : C ≤ C')
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  condBcProb G C p q F ψ a * condBcProb G C' p q F ψ b ≤ condBcProb G C p q F ψ (a ⊓ b) * condBcProb G C' p q F ψ (a ⊔ b) := by
-- proof
  apply StatMech.FK.condBcProb_cross G C C' hCC' hp hp1 hq F ψ a b

/--
[condBcProb_mono_bc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean)
-/
@[path]
private lemma condBcProb_mono_bc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hCC' : C ≤ C')
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * condBcProb G C p q F ψ ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * condBcProb G C' p q F ψ ω := by
-- proof
  apply StatMech.FK.condBcProb_mono_bc G C C' hCC' hp hp1 hq F ψ hA

/--
[bcProb_eq_fibreMass_mul_condBcProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean)
-/
@[path]
private lemma bcProb_eq_fibreMass_mul_condBcProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  bcProb G C p q ω = (∑ ρ ∈ condFibre F ω, bcProb G C p q ρ) * condBcProb G C p q F ω ω := by
-- proof
  apply StatMech.FK.bcProb_eq_fibreMass_mul_condBcProb G C hp hp1 hq F ω

/--
[condBcProb_average_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean)
-/
@[path]
private lemma condBcProb_average_mono_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hCC' : C ≤ C')
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C' p q ω := by
-- proof
  apply StatMech.FK.condBcProb_average_mono G C C' hCC' hp hp1 hq hA

/--
[wiredFkProb_inner_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean)
-/
@[path]
private lemma wiredFkProb_inner_dominated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidablePred bdry]
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (bdry : V → Prop)
  (hCC' : StatMech.Lattice.boundaryCliqueGraph bdry ≤ C')
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * wiredFkProb G bdry p q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C' p q ω := by
-- proof
  apply StatMech.FK.wiredFkProb_inner_dominated G C bdry C' hCC' hp hp1 hq hA

/--
[wiredFkProb_inner_dominated_cond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean)
-/
@[path]
private lemma wiredFkProb_inner_dominated_cond_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidablePred bdry]
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (bdry : V → Prop)
  (hCC' : StatMech.Lattice.boundaryCliqueGraph bdry ≤ C')
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * condBcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q F ψ ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * condBcProb G C' p q F ψ ω := by
-- proof
  apply StatMech.FK.wiredFkProb_inner_dominated_cond G C bdry C' hCC' hp hp1 hq F ψ hA


-- created on 2026-10-23
