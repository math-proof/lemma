import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.fkuniqclose
open MeasureTheory Filter Topology Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[fku_free_eq_wired_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkuniqclose.lean)
-/
@[path]
private lemma fku_free_eq_wired_cylinder_eq
  {d : ℕ}
  {p : ℝ}
  {N : ℕ}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hbad : p ∉ fwa_badP d)
  (hN : 1 ≤ N)
  (hA : IsIncreasing A) :
-- imply
  (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) := by
-- proof
  apply StatMech.FK.fku_free_eq_wired_cylinder hd hp hp1 hbad hN hA

/--
[fku_unique_off_countable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkuniqclose.lean)
-/
@[path]
private lemma fku_unique_off_countable_eq
  {d : ℕ}
  {p : ℝ}
  {phi : Measure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hbad : p ∉ fwa_badP d)
  (hsand : ∀ (N : ℕ), 1 ≤ N → ∀ {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing A → (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) ≤ phi.real (boxRestrict d N ⁻¹' A) ∧ phi.real (boxRestrict d N ⁻¹' A) ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A)) :
-- imply
  ∀ (N : ℕ), 1 ≤ N → ∀ {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing A → phi.real (boxRestrict d N ⁻¹' A) = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) ∧ phi.real (boxRestrict d N ⁻¹' A) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) := by
-- proof
  apply StatMech.FK.fku_unique_off_countable hd hp hp1 hbad phi hsand

/--
[fku_uniqueness_capstone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkuniqclose.lean)
-/
@[path]
private lemma fku_uniqueness_capstone_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  ∃ S : Set ℝ, S.Countable ∧ ∀ p, 0 < p → p < 1 → p ∉ S → ∀ (hp : 0 < p) (hp1 : p < 1) (phi : Measure (ConfigSpace (Sym2 (Site d)))), (∀ (N : ℕ), 1 ≤ N → ∀ {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing A → (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) ≤ phi.real (boxRestrict d N ⁻¹' A) ∧ phi.real (boxRestrict d N ⁻¹' A) ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A)) → ∀ (N : ℕ), 1 ≤ N → ∀ {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing A → phi.real (boxRestrict d N ⁻¹' A) = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) ∧ phi.real (boxRestrict d N ⁻¹' A) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) := by
-- proof
  apply StatMech.FK.fku_uniqueness_capstone hd

/--
[fku_exists_good](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkuniqclose.lean)
-/
@[path]
private lemma fku_exists_good_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  ∃ p : ℝ, 0 < p ∧ p < 1 ∧ p ∉ fwa_badP d := by
-- proof
  apply StatMech.FK.fku_exists_good hd


-- created on 2026-10-23
