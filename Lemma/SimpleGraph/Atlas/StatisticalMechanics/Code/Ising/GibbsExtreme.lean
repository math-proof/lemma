import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
open StatMech.Ising StatMech.Lattice Finset MeasureTheory Set StatMech


/--
[spinB_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma spinB_mono_eq
  {d : ℕ}
  {p q : Bool}
-- given
  (h : p ≤ q) :
-- imply
  (if p then (1 : ℝ) else -1) ≤ (if q then 1 else -1) := by
-- proof
  apply StatMech.Ising.spinB_mono p q h

/--
[spinB_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma spinB_inf_eq
  {d : ℕ}
  {p q : Bool} :
-- imply
  (if (p ⊓ q) then (1 : ℝ) else -1) = min (if p then 1 else -1) (if q then 1 else -1) := by
-- proof
  apply StatMech.Ising.spinB_inf p q

/--
[spinB_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma spinB_sup_eq
  {d : ℕ}
  {p q : Bool} :
-- imply
  (if (p ⊔ q) then (1 : ℝ) else -1) = max (if p then 1 else -1) (if q then 1 else -1) := by
-- proof
  apply StatMech.Ising.spinB_sup p q

/--
[glue_mono_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma glue_mono_interior_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
-- given
  (τ τ' : {x // x ∈ box d n} → Bool)
  (h : τ ≤ τ') :
-- imply
  glue η τ ≤ glue η τ' := by
-- proof
  apply StatMech.Ising.glue_mono_interior η τ τ' h

/--
[glue_mono_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma glue_mono_boundary_eq
  {d : ℕ}
  {n : ℕ}
  {η η' : ConfigSpace (Site d)}
-- given
  (hle : η ≤ η')
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  glue η τ ≤ glue η' τ := by
-- proof
  apply StatMech.Ising.glue_mono_boundary η η' hle τ

/--
[spin_glue_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma spin_glue_inf_eq
  {d : ℕ}
  {n : ℕ}
  {η η' : ConfigSpace (Site d)}
  {x : Site d}
-- given
  (hle : η ≤ η')
  (a b : {x // x ∈ box d n} → Bool) :
-- imply
  spin (glue η (a ⊓ b)) x = min (spin (glue η a) x) (spin (glue η' b) x) := by
-- proof
  apply StatMech.Ising.spin_glue_inf n η η' hle a b x

/--
[spin_glue_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma spin_glue_sup_eq
  {d : ℕ}
  {n : ℕ}
  {η η' : ConfigSpace (Site d)}
  {x : Site d}
-- given
  (hle : η ≤ η')
  (a b : {x // x ∈ box d n} → Bool) :
-- imply
  spin (glue η' (a ⊔ b)) x = max (spin (glue η a) x) (spin (glue η' b) x) := by
-- proof
  apply StatMech.Ising.spin_glue_sup n η η' hle a b x

/--
[prod_supermod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma prod_supermod_eq
  {d : ℕ}
  {u₁ u₂ v₁ v₂ : ℝ} :
-- imply
  u₁ * v₁ + u₂ * v₂ ≤ min u₁ u₂ * min v₁ v₂ + max u₁ u₂ * max v₁ v₂ := by
-- proof
  apply StatMech.Ising.prod_supermod u₁ u₂ v₁ v₂

/--
[bond_glue_supermod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma bond_glue_supermod_eq
  {d : ℕ}
  {n : ℕ}
  {η η' : ConfigSpace (Site d)}
  {e : Sym2 (Site d)}
-- given
  (hle : η ≤ η')
  (a b : {x // x ∈ box d n} → Bool) :
-- imply
  bond (glue η a) e + bond (glue η' b) e ≤ bond (glue η (a ⊓ b)) e + bond (glue η' (a ⊔ b)) e := by
-- proof
  apply StatMech.Ising.bond_glue_supermod n η η' hle a b e

/--
[spin_glue_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma spin_glue_add_eq
  {d : ℕ}
  {n : ℕ}
  {η η' : ConfigSpace (Site d)}
  {x : Site d}
-- given
  (hle : η ≤ η')
  (a b : {x // x ∈ box d n} → Bool) :
-- imply
  spin (glue η a) x + spin (glue η' b) x = spin (glue η (a ⊓ b)) x + spin (glue η' (a ⊔ b)) x := by
-- proof
  apply StatMech.Ising.spin_glue_add n η η' hle a b x

/--
[fvEnergy_supermod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma fvEnergy_supermod_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {η η' : ConfigSpace (Site d)}
-- given
  (h : ℝ)
  (hh : 0 ≤ h)
  (hle : η ≤ η')
  (a b : {x // x ∈ box d n} → Bool) :
-- imply
  fvEnergy η n B h (a ⊓ b) + fvEnergy η' n B h (a ⊔ b) ≤ fvEnergy η n B h a + fvEnergy η' n B h b := by
-- proof
  apply StatMech.Ising.fvEnergy_supermod n B h hh η η' hle a b

/--
[fvWeight_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma fvWeight_cross_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {η η' : ConfigSpace (Site d)}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hle : η ≤ η')
  (a b : {x // x ∈ box d n} → Bool) :
-- imply
  fvWeight η n B β h a * fvWeight η' n B β h b ≤ fvWeight η n B β h (a ⊓ b) * fvWeight η' n B β h (a ⊔ b) := by
-- proof
  apply StatMech.Ising.fvWeight_cross n B β h hβ hh η η' hle a b

/--
[fvProb_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma fvProb_cross_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {η η' : ConfigSpace (Site d)}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hle : η ≤ η')
  (a b : ConfigSpace {x // x ∈ box d n}) :
-- imply
  fvProb η n B β h a * fvProb η' n B β h b ≤ fvProb η n B β h (a ⊓ b) * fvProb η' n B β h (a ⊔ b) := by
-- proof
  apply StatMech.Ising.fvProb_cross n B β h hβ hh η η' hle a b

/--
[fvProb_dominates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma fvProb_dominates_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {η η' : ConfigSpace (Site d)}
  {A : Set (ConfigSpace {x // x ∈ box d n})}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hle : η ≤ η')
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fvProb η n B β h ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fvProb η' n B β h ω := by
-- proof
  apply StatMech.Ising.fvProb_dominates n B β h hβ hh η η' hle hA

/--
[fvMeasure_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma fvMeasure_real_eq_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {A : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (hA : MeasurableSet A) :
-- imply
  (fvMeasure η n B β h).real A = ∑ τ : {x // x ∈ box d n} → Bool, fvProb η n B β h τ * (Set.indicator A (fun _ => (1 : ℝ)) (glue η τ)) := by
-- proof
  apply StatMech.Ising.fvMeasure_real_eq η n B β h hA

/--
[fvMeasure_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma fvMeasure_dominated_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {η η' : ConfigSpace (Site d)}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hle : η ≤ η') :
-- imply
  (fvMeasure η n B β h) ≼ (fvMeasure η' n B β h) := by
-- proof
  apply StatMech.Ising.fvMeasure_dominated n B β h hβ hh η η' hle

/--
[minusField_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma minusField_le_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)} :
-- imply
  minusField d ≤ η := by
-- proof
  apply StatMech.Ising.minusField_le η

/--
[le_plusField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma le_plusField_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)} :
-- imply
  η ≤ plusField d := by
-- proof
  apply StatMech.Ising.le_plusField η

/--
[fvMeasure_minusField_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma fvMeasure_minusField_le_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {η : ConfigSpace (Site d)}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  (fvMeasure (minusField d) n B β h) ≼ (fvMeasure η n B β h) := by
-- proof
  apply StatMech.Ising.fvMeasure_minusField_le n B β h hβ hh η

/--
[fvMeasure_le_plusField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma fvMeasure_le_plusField_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {η : ConfigSpace (Site d)}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  (fvMeasure η n B β h) ≼ (fvMeasure (plusField d) n B β h) := by
-- proof
  apply StatMech.Ising.fvMeasure_le_plusField n B β h hβ hh η

/--
[fvMeasure_minus_sandwich_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma fvMeasure_minus_sandwich_plus_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {η : ConfigSpace (Site d)}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  (fvMeasure (minusField d) n B β h) ≼ (fvMeasure η n B β h) ∧ (fvMeasure η n B β h) ≼ (fvMeasure (plusField d) n B β h) := by
-- proof
  apply StatMech.Ising.fvMeasure_minus_sandwich_plus n B β h hβ hh η

/--
[fvMeasure_minus_le_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean)
-/
@[path]
private lemma fvMeasure_minus_le_plus_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  (fvMeasure (minusField d) n B β h) ≼ (fvMeasure (plusField d) n B β h) := by
-- proof
  apply StatMech.Ising.fvMeasure_minus_le_plus n B β h hβ hh


-- created on 2026-10-23
