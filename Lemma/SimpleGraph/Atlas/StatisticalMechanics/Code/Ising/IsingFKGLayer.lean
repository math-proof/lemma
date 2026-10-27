import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
open Finset StatMech StatMech.Ising


/--
[ifk_bond_supermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_bond_supermodular_eq
  {a b : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  bond a e + bond b e ≤ bond (a ⊔ b) e + bond (a ⊓ b) e := by
-- proof
  apply StatMech.Ising.ifk_bond_supermodular a b e

/--
[ifk_spin_modular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_spin_modular_eq
  {a b : ConfigSpace V}
  {x : V} :
-- imply
  spin a x + spin b x = spin (a ⊔ b) x + spin (a ⊓ b) x := by
-- proof
  apply StatMech.Ising.ifk_spin_modular a b x

/--
[ifk_spin_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_spin_mono_eq
  {a b : ConfigSpace V}
  {x : V}
-- given
  (hab : a ≤ b) :
-- imply
  spin a x ≤ spin b x := by
-- proof
  apply StatMech.Ising.ifk_spin_mono hab x

/--
[ifk_hamiltonian_submodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_hamiltonian_submodular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : ConfigSpace V}
-- given
  (h : ℝ) :
-- imply
  hamiltonian G h (a ⊔ b) + hamiltonian G h (a ⊓ b) ≤ hamiltonian G h a + hamiltonian G h b := by
-- proof
  apply StatMech.Ising.ifk_hamiltonian_submodular G h a b

/--
[ifk_isingWeight_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_isingWeight_logSupermodular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {a b : ConfigSpace V}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ) :
-- imply
  isingWeight G β h a * isingWeight G β h b ≤ isingWeight G β h (a ⊔ b) * isingWeight G β h (a ⊓ b) := by
-- proof
  apply StatMech.Ising.ifk_isingWeight_logSupermodular G hβ h a b

/--
[ifk_isingProb_FKGLatticeCondition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_isingProb_FKGLatticeCondition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ) :
-- imply
  FKGLatticeCondition (fun s => isingProb G β h s) := by
-- proof
  apply StatMech.Ising.ifk_isingProb_FKGLatticeCondition G hβ h

/--
[ifk_isingProb_positively_associated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_isingProb_positively_associated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {f g : ConfigSpace V → ℝ}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  (∑ s, isingProb G β h s * f s) * (∑ s, isingProb G β h s * g s) ≤ ∑ s, isingProb G β h s * (f s * g s) := by
-- proof
  apply StatMech.Ising.ifk_isingProb_positively_associated G hβ h hf hg

/--
[ifk_isingProb_positively_associated_events](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_isingProb_positively_associated_events_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {A B : Set (ConfigSpace V)}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  (∑ s, isingProb G β h s * A.indicator (fun _ => (1 : ℝ)) s) * (∑ s, isingProb G β h s * B.indicator (fun _ => (1 : ℝ)) s) ≤ ∑ s, isingProb G β h s * (A ∩ B).indicator (fun _ => (1 : ℝ)) s := by
-- proof
  apply StatMech.Ising.ifk_isingProb_positively_associated_events G hβ h hA hB

/--
[ifk_glue_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_glue_sup_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
-- given
  (τ τ' : {x // x ∈ box d n} → Bool) :
-- imply
  glue η (τ ⊔ τ') = glue η τ ⊔ glue η τ' := by
-- proof
  apply StatMech.Ising.ifk_glue_sup G η τ τ'

/--
[ifk_glue_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_glue_inf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
-- given
  (τ τ' : {x // x ∈ box d n} → Bool) :
-- imply
  glue η (τ ⊓ τ') = glue η τ ⊓ glue η τ' := by
-- proof
  apply StatMech.Ising.ifk_glue_inf G η τ τ'

/--
[ifk_fvEnergy_submodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_fvEnergy_submodular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (h : ℝ)
  (τ τ' : {x // x ∈ box d n} → Bool) :
-- imply
  fvEnergy η n B h (τ ⊔ τ') + fvEnergy η n B h (τ ⊓ τ') ≤ fvEnergy η n B h τ + fvEnergy η n B h τ' := by
-- proof
  apply StatMech.Ising.ifk_fvEnergy_submodular G η n B h τ τ'

/--
[ifk_fvWeight_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_fvWeight_logSupermodular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (τ τ' : {x // x ∈ box d n} → Bool) :
-- imply
  fvWeight η n B β h τ * fvWeight η n B β h τ' ≤ fvWeight η n B β h (τ ⊔ τ') * fvWeight η n B β h (τ ⊓ τ') := by
-- proof
  apply StatMech.Ising.ifk_fvWeight_logSupermodular G η n B hβ h τ τ'

/--
[ifk_fvProb_FKGLatticeCondition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_fvProb_FKGLatticeCondition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ) :
-- imply
  FKGLatticeCondition (fun τ : {x // x ∈ box d n} → Bool => fvProb η n B β h τ) := by
-- proof
  apply StatMech.Ising.ifk_fvProb_FKGLatticeCondition G η n B hβ h

/--
[ifk_fvProb_positively_associated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_fvProb_positively_associated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {β : ℝ}
  {f g : ({x // x ∈ box d n} → Bool) → ℝ}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  (∑ τ, fvProb η n B β h τ * f τ) * (∑ τ, fvProb η n B β h τ * g τ) ≤ ∑ τ, fvProb η n B β h τ * (f τ * g τ) := by
-- proof
  apply StatMech.Ising.ifk_fvProb_positively_associated G η n B hβ h hf hg

/--
[ifk_fvProb_positively_associated_events](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_fvProb_positively_associated_events_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {β : ℝ}
  {A B' : Set (ConfigSpace {x // x ∈ box d n})}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B') :
-- imply
  (∑ τ, fvProb η n B β h τ * A.indicator (fun _ => (1 : ℝ)) τ) * (∑ τ, fvProb η n B β h τ * B'.indicator (fun _ => (1 : ℝ)) τ) ≤ ∑ τ, fvProb η n B β h τ * (A ∩ B').indicator (fun _ => (1 : ℝ)) τ := by
-- proof
  apply StatMech.Ising.ifk_fvProb_positively_associated_events G η n B hβ h hA hB

/--
[ifk_glue_cross_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_glue_cross_inf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {η₁ η₂ : ConfigSpace (Site d)}
  {n : ℕ}
-- given
  (hη : η₁ ≤ η₂)
  (a b : {x // x ∈ box d n} → Bool) :
-- imply
  glue η₁ (a ⊓ b) = glue η₁ a ⊓ glue η₂ b := by
-- proof
  apply StatMech.Ising.ifk_glue_cross_inf G hη a b

/--
[ifk_glue_cross_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_glue_cross_sup_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {η₁ η₂ : ConfigSpace (Site d)}
  {n : ℕ}
-- given
  (hη : η₁ ≤ η₂)
  (a b : {x // x ∈ box d n} → Bool) :
-- imply
  glue η₂ (a ⊔ b) = glue η₁ a ⊔ glue η₂ b := by
-- proof
  apply StatMech.Ising.ifk_glue_cross_sup G hη a b

/--
[ifk_fvEnergy_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_fvEnergy_cross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {η₁ η₂ : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (hη : η₁ ≤ η₂)
  (h : ℝ)
  (a b : {x // x ∈ box d n} → Bool) :
-- imply
  fvEnergy η₁ n B h (a ⊓ b) + fvEnergy η₂ n B h (a ⊔ b) ≤ fvEnergy η₁ n B h a + fvEnergy η₂ n B h b := by
-- proof
  apply StatMech.Ising.ifk_fvEnergy_cross G hη n B h a b

/--
[ifk_fvWeight_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_fvWeight_cross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {η₁ η₂ : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {β : ℝ}
-- given
  (hη : η₁ ≤ η₂)
  (hβ : 0 ≤ β)
  (h : ℝ)
  (a b : {x // x ∈ box d n} → Bool) :
-- imply
  fvWeight η₁ n B β h a * fvWeight η₂ n B β h b ≤ fvWeight η₁ n B β h (a ⊓ b) * fvWeight η₂ n B β h (a ⊔ b) := by
-- proof
  apply StatMech.Ising.ifk_fvWeight_cross G hη n B hβ h a b

/--
[ifk_fvProb_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_fvProb_cross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {η₁ η₂ : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {β : ℝ}
-- given
  (hη : η₁ ≤ η₂)
  (hβ : 0 ≤ β)
  (h : ℝ)
  (a b : {x // x ∈ box d n} → Bool) :
-- imply
  fvProb η₁ n B β h a * fvProb η₂ n B β h b ≤ fvProb η₁ n B β h (a ⊓ b) * fvProb η₂ n B β h (a ⊔ b) := by
-- proof
  apply StatMech.Ising.ifk_fvProb_cross G hη n B hβ h a b

/--
[ifk_fvProb_holley_dominates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_fvProb_holley_dominates_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {η₁ η₂ : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {β : ℝ}
  {A : Set (ConfigSpace {x // x ∈ box d n})}
-- given
  (hη : η₁ ≤ η₂)
  (hβ : 0 ≤ β)
  (h : ℝ)
  (hA : IsIncreasing A) :
-- imply
  ∑ τ, A.indicator (fun _ => (1 : ℝ)) τ * fvProb η₁ n B β h τ ≤ ∑ τ, A.indicator (fun _ => (1 : ℝ)) τ * fvProb η₂ n B β h τ := by
-- proof
  apply StatMech.Ising.ifk_fvProb_holley_dominates G hη n B hβ h hA

/--
[ifk_minusField_le_plusField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_minusField_le_plusField_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {d : ℕ} :
-- imply
  minusField d ≤ plusField d := by
-- proof
  apply StatMech.Ising.ifk_minusField_le_plusField G d

/--
[ifk_minus_le_plus_dominates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_minus_le_plus_dominates_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {n : ℕ}
  {β : ℝ}
  {A : Set (ConfigSpace {x // x ∈ box d n})}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (hA : IsIncreasing A) :
-- imply
  ∑ τ, A.indicator (fun _ => (1 : ℝ)) τ * fvProb (minusField d) n (bondFinsetTouch d n) β h τ ≤ ∑ τ, A.indicator (fun _ => (1 : ℝ)) τ * fvProb (plusField d) n (bondFinsetTouch d n) β h τ := by
-- proof
  apply StatMech.Ising.ifk_minus_le_plus_dominates G n hβ h hA

/--
[ifk_isIncreasing_siteUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_isIncreasing_siteUp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {n : ℕ}
-- given
  (x : {x // x ∈ box d n}) :
-- imply
  IsIncreasing {τ : ConfigSpace {x // x ∈ box d n} | τ x = true} := by
-- proof
  apply StatMech.Ising.ifk_isIncreasing_siteUp G n x

/--
[ifk_minus_le_plus_siteUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean)
-/
@[path]
private lemma ifk_minus_le_plus_siteUp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {n : ℕ}
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (x : {x // x ∈ box d n}) :
-- imply
  ∑ τ, {τ : ConfigSpace {x // x ∈ box d n} | τ x = true}.indicator (fun _ => (1 : ℝ)) τ * fvProb (minusField d) n (bondFinsetTouch d n) β h τ ≤ ∑ τ, {τ : ConfigSpace {x // x ∈ box d n} | τ x = true}.indicator (fun _ => (1 : ℝ)) τ * fvProb (plusField d) n (bondFinsetTouch d n) β h τ := by
-- proof
  apply StatMech.Ising.ifk_minus_le_plus_siteUp G n hβ h x


-- created on 2026-10-23
