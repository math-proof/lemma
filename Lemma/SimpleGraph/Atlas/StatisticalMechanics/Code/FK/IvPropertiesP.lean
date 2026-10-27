import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.IvPropertiesP
open MeasureTheory Filter Topology SimpleGraph StatMech.Lattice StatMech.IsingFK StatMech StatMech.FK


/--
[freeFiniteMeasure_real_monotone_in_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvPropertiesP.lean)
-/
@[path]
private lemma freeFiniteMeasure_real_monotone_in_p_eq
  {d : ℕ}
  {m : ℕ}
  {p₁ p₂ : ℝ}
  {T : Set (ConfigSpace (Sym2 (boxVerts d m)))}
-- given
  (hp₁ : 0 < p₁)
  (hp₁' : p₁ < 1)
  (hp₂ : 0 < p₂)
  (hp₂' : p₂ < 1)
  (hle : p₁ ≤ p₂)
  (hT : IsIncreasing T)
  (hmeas : MeasurableSet (boxRestrict d m ⁻¹' T)) :
-- imply
  (freeFiniteMeasure d m hp₁ hp₁' (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' T) ≤ (freeFiniteMeasure d m hp₂ hp₂' (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' T) := by
-- proof
  apply StatMech.FK.freeFiniteMeasure_real_monotone_in_p m hp₁ hp₁' hp₂ hp₂' hle hT hmeas

/--
[freeFiniteMeasure_real_monotone_in_p_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvPropertiesP.lean)
-/
@[path]
private lemma freeFiniteMeasure_real_monotone_in_p_inner_eq
  {d : ℕ}
  {N m : ℕ}
  {p₁ p₂ : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hp₁ : 0 < p₁)
  (hp₁' : p₁ < 1)
  (hp₂ : 0 < p₂)
  (hp₂' : p₂ < 1)
  (hle : p₁ ≤ p₂)
  (hS : IsIncreasing S) :
-- imply
  (freeFiniteMeasure d m hp₁ hp₁' (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) ≤ (freeFiniteMeasure d m hp₂ hp₂' (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.freeFiniteMeasure_real_monotone_in_p_inner N m hNm hp₁ hp₁' hp₂ hp₂' hle hS

/--
[ivp_free_iv_monotone_in_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvPropertiesP.lean)
-/
@[path]
private lemma ivp_free_iv_monotone_in_p_eq
  {d : ℕ}
  {N : ℕ}
  {p₁ p₂ : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp₁ : 0 < p₁)
  (hp₁' : p₁ < 1)
  (hp₂ : 0 < p₂)
  (hp₂' : p₂ < 1)
  (hle : p₁ ≤ p₂)
  (hS : IsIncreasing S) :
-- imply
  (freeInfiniteVolume d hp₁ hp₁' (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) ≤ (freeInfiniteVolume d hp₂ hp₂' (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.ivp_free_iv_monotone_in_p N hp₁ hp₁' hp₂ hp₂' hle hS

/--
[ivp_wired_iv_monotone_in_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvPropertiesP.lean)
-/
@[path]
private lemma ivp_wired_iv_monotone_in_p_eq
  {d : ℕ}
  {N : ℕ}
  {p₁ p₂ : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp₁ : 0 < p₁)
  (hp₁' : p₁ < 1)
  (hp₂ : 0 < p₂)
  (hp₂' : p₂ < 1)
  (hle : p₁ ≤ p₂)
  (hS : IsIncreasing S) :
-- imply
  (wiredInfiniteVolume d hp₁ hp₁' (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) ≤ (wiredInfiniteVolume d hp₂ hp₂' (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.ivp_wired_iv_monotone_in_p N hp₁ hp₁' hp₂ hp₂' hle hS


-- created on 2026-10-23
