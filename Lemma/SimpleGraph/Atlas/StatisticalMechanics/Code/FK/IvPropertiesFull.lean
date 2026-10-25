import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.IvPropertiesFull
open MeasureTheory Filter Topology SimpleGraph StatMech.Lattice StatMech.IsingFK StatMech StatMech.FK


/--
[freeFiniteMeasure_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvPropertiesFull.lean)
-/
@[path]
private lemma freeFiniteMeasure_fkg_eq
  {d : ℕ}
  {N m : ℕ}
  {p : ℝ}
  {S₁ S₂ : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS₁ : IsIncreasing S₁)
  (hS₂ : IsIncreasing S₂) :
-- imply
  (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁) * (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₂) ≤ (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂) := by
-- proof
  apply StatMech.FK.freeFiniteMeasure_fkg N m hNm hp hp1 hS₁ hS₂

/--
[ivp_iv_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvPropertiesFull.lean)
-/
@[path]
private lemma ivp_iv_fkg_eq
  {d : ℕ}
  {N : ℕ}
  {p : ℝ}
  {S₁ S₂ : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS₁ : IsIncreasing S₁)
  (hS₂ : IsIncreasing S₂) :
-- imply
  (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁) * (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₂) ≤ (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂) := by
-- proof
  apply StatMech.FK.ivp_iv_fkg N hp hp1 hS₁ hS₂

/--
[wiredFkProb_eq_bcProb_clique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvPropertiesFull.lean)
-/
@[path]
private lemma wiredFkProb_eq_bcProb_clique_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  wiredFkProb G bdry p q ω = bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω := by
-- proof
  apply StatMech.FK.wiredFkProb_eq_bcProb_clique G bdry p q ω

/--
[wiredFkProb_FKGLatticeCondition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvPropertiesFull.lean)
-/
@[path]
private lemma wiredFkProb_FKGLatticeCondition_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  FKGLatticeCondition (fun ω => wiredFkProb G bdry p q ω) := by
-- proof
  apply StatMech.FK.wiredFkProb_FKGLatticeCondition G bdry hp hp1 hq

/--
[wiredFkProb_positively_associated_events](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvPropertiesFull.lean)
-/
@[path]
private lemma wiredFkProb_positively_associated_events_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
  {A B : Set (ConfigSpace (Sym2 V))}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  (∑ ω, wiredFkProb G bdry p q ω * A.indicator (fun _ => (1 : ℝ)) ω) * (∑ ω, wiredFkProb G bdry p q ω * B.indicator (fun _ => (1 : ℝ)) ω) ≤ ∑ ω, wiredFkProb G bdry p q ω * (A ∩ B).indicator (fun _ => (1 : ℝ)) ω := by
-- proof
  apply StatMech.FK.wiredFkProb_positively_associated_events G bdry hp hp1 hq hA hB

/--
[wiredFiniteMeasure_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvPropertiesFull.lean)
-/
@[path]
private lemma wiredFiniteMeasure_fkg_eq
  {d : ℕ}
  {N m : ℕ}
  {p : ℝ}
  {S₁ S₂ : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS₁ : IsIncreasing S₁)
  (hS₂ : IsIncreasing S₂) :
-- imply
  (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁) * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₂) ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂) := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_fkg N m hNm hp hp1 hS₁ hS₂

/--
[ivp_iv_fkg_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvPropertiesFull.lean)
-/
@[path]
private lemma ivp_iv_fkg_wired_eq
  {d : ℕ}
  {N : ℕ}
  {p : ℝ}
  {S₁ S₂ : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS₁ : IsIncreasing S₁)
  (hS₂ : IsIncreasing S₂) :
-- imply
  (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁) * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₂) ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂) := by
-- proof
  apply StatMech.FK.ivp_iv_fkg_wired N hp hp1 hS₁ hS₂

/--
[ivp_iv_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvPropertiesFull.lean)
-/
@[path]
private lemma ivp_iv_monotone_eq
  {d : ℕ}
  {N : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.ivp_iv_monotone N hp hp1 hS


-- created on 2026-10-23
