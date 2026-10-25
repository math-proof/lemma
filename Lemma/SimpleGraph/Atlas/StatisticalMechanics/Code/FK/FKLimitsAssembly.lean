import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.FKLimitsAssembly
open MeasureTheory Filter Topology StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[fla_fk_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsAssembly.lean)
-/
@[path]
private lemma fla_fk_limits_eq
  {d : ℕ}
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hextW : ∀ (ν₁ ν₂ : Measure (ConfigSpace (Sym2 (Site d)))) (a b : ℝ≥0∞), IsTranslationInvariant (G := Multiplicative (Site d)) ν₁ → IsTranslationInvariant (G := Multiplicative (Site d)) ν₂ → IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ → 0 < a → 0 < b → a + b = 1 → (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) = a • ν₁ + b • ν₂ → ν₁ = ν₂)
  (hextF : ∀ (ν₁ ν₂ : Measure (ConfigSpace (Sym2 (Site d)))) (a b : ℝ≥0∞), IsTranslationInvariant (G := Multiplicative (Site d)) ν₁ → IsTranslationInvariant (G := Multiplicative (Site d)) ν₂ → IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ → 0 < a → 0 < b → a + b = 1 → (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) = a • ν₁ + b • ν₂ → ν₁ = ν₂) :
-- imply
  (∀ (N : ℕ) {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing S → Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)))) ∧ (∀ (N : ℕ) {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing S → Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)))) ∧ IsTranslationInvariant (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) ∧ IsTranslationInvariant (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) ∧ IsErgodic (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) ∧ IsErgodic (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) ∧ (∀ (N : ℕ) {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing S → (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) := by
-- proof
  apply StatMech.FK.fla_fk_limits d hd hp hp1 hextW hextF


-- created on 2026-10-23
