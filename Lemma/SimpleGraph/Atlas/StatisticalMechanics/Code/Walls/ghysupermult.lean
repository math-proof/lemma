import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.ghysupermult.Part2
open Finset BigOperators Classical StatMech StatMech.Walls


/--
[ghy_ZJ_insert_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghysupermult.lean)
-/
@[path]
private lemma ghy_ZJ_insert_factor_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {x y : V}
-- given
  (hf : V → ℝ)
  (hxy : x ≠ y)
  (he : s(x, y) ∉ E) :
-- imply
  ZJ (insert s(x, y) E) J hf = ZJ E J hf * (Real.cosh (J s(x, y)) + Real.sinh (J s(x, y)) * expJ E J hf (spinProd {x, y})) := by
-- proof
  apply StatMech.Walls.ghy_ZJ_insert_factor E J hf hxy he

/--
[ghy_ratio_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghysupermult.lean)
-/
@[path]
private lemma ghy_ratio_insert_eq
  [Fintype V]
  [DecidableEq V]
  {C D : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {x y : V}
-- given
  (hf : V → ℝ)
  (hJ : ∀ e, 0 ≤ J e)
  (hhf : ∀ v, 0 ≤ hf v)
  (hCD : C ⊆ D)
  (hnd : ∀ e ∈ D, ¬ e.IsDiag)
  (hxy : x ≠ y)
  (heD : s(x, y) ∉ D) :
-- imply
  ZJ (insert s(x, y) C) J hf * ZJ D J hf ≤ ZJ (insert s(x, y) D) J hf * ZJ C J hf := by
-- proof
  apply StatMech.Walls.ghy_ratio_insert C D J hf hJ hhf hCD hnd hxy heD

/--
[ghy_ZJ_supermod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghysupermult.lean)
-/
@[path]
private lemma ghy_ZJ_supermod_eq
  [Fintype V]
  [DecidableEq V]
  {J : Sym2 V → ℝ}
  {C D : Finset (Sym2 V)}
-- given
  (hf : V → ℝ)
  (hJ : ∀ e, 0 ≤ J e)
  (hhf : ∀ v, 0 ≤ hf v)
  (hCD : C ⊆ D)
  (hndD : ∀ e ∈ D, ¬ e.IsDiag) :
-- imply
  ∀ P : Finset (Sym2 V), Disjoint P D → (∀ e ∈ P, ¬ e.IsDiag) → ZJ (C ∪ P) J hf * ZJ D J hf ≤ ZJ (D ∪ P) J hf * ZJ C J hf := by
-- proof
  apply StatMech.Walls.ghy_ZJ_supermod J hf hJ hhf C D hCD hndD

/--
[ghy_Zdep_supermod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghysupermult.lean)
-/
@[path]
private lemma ghy_Zdep_supermod_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {S₁ S₂ : Finset (Sym2 V)}
-- given
  (hf : V → ℝ)
  (hJ : ∀ e, 0 ≤ J e)
  (hhf : ∀ v, 0 ≤ hf v)
  (hndE : ∀ e ∈ E, ¬ e.IsDiag)
  (hS₁ : S₁ ⊆ E)
  (hS₂ : S₂ ⊆ E)
  (hdisj : Disjoint S₁ S₂) :
-- imply
  ZJ (E \ S₁) J hf * ZJ (E \ S₂) J hf ≤ ZJ E J hf * ZJ (E \ (S₁ ∪ S₂)) J hf := by
-- proof
  apply StatMech.Walls.ghy_Zdep_supermod E J hf hJ hhf hndE S₁ S₂ hS₁ hS₂ hdisj

/--
[ghy_zeta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghysupermult.lean)
-/
@[path]
private lemma ghy_zeta_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {S : Finset (Sym2 V)}
-- given
  (hf : V → ℝ) :
-- imply
  0 ≤ ghy_zeta E J hf S := by
-- proof
  apply StatMech.Walls.ghy_zeta_nonneg E J hf S

/--
[ghy_tanh_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghysupermult.lean)
-/
@[path]
private lemma ghy_tanh_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {t : ℝ}
-- given
  (ht : 0 ≤ t) :
-- imply
  0 ≤ Real.tanh t := by
-- proof
  apply StatMech.Walls.ghy_tanh_nonneg ht

/--
[ghy_rho_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghysupermult.lean)
-/
@[path]
private lemma ghy_rho_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {S : Finset (Sym2 V)}
-- given
  (hf : V → ℝ)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ ghy_rho E J hf S := by
-- proof
  apply StatMech.Walls.ghy_rho_nonneg E J hf hJ S

/--
[ghy_zeta_supermult](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghysupermult.lean)
-/
@[path]
private lemma ghy_zeta_supermult_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {S₁ S₂ : Finset (Sym2 V)}
-- given
  (hf : V → ℝ)
  (hJ : ∀ e, 0 ≤ J e)
  (hhf : ∀ v, 0 ≤ hf v)
  (hndE : ∀ e ∈ E, ¬ e.IsDiag)
  (hS₁ : S₁ ⊆ E)
  (hS₂ : S₂ ⊆ E)
  (hdisj : Disjoint S₁ S₂) :
-- imply
  ghy_zeta E J hf S₁ * ghy_zeta E J hf S₂ ≤ ghy_zeta E J hf (S₁ ∪ S₂) := by
-- proof
  apply StatMech.Walls.ghy_zeta_supermult E J hf hJ hhf hndE S₁ S₂ hS₁ hS₂ hdisj

/--
[ghy_rho_supermult](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghysupermult.lean)
-/
@[path]
private lemma ghy_rho_supermult_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {S₁ S₂ : Finset (Sym2 V)}
-- given
  (hf : V → ℝ)
  (hJ : ∀ e, 0 ≤ J e)
  (hhf : ∀ v, 0 ≤ hf v)
  (hndE : ∀ e ∈ E, ¬ e.IsDiag)
  (hS₁ : S₁ ⊆ E)
  (hS₂ : S₂ ⊆ E)
  (hdisj : Disjoint S₁ S₂) :
-- imply
  ghy_rho E J hf S₁ * ghy_rho E J hf S₂ ≤ ghy_rho E J hf (S₁ ∪ S₂) := by
-- proof
  apply StatMech.Walls.ghy_rho_supermult E J hf hJ hhf hndE S₁ S₂ hS₁ hS₂ hdisj

/--
[ghy_rho_supermult_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghysupermult.lean)
-/
@[path]
private lemma ghy_rho_supermult_three_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {S₁ S₂ S₃ : Finset (Sym2 V)}
-- given
  (hf : V → ℝ)
  (hJ : ∀ e, 0 ≤ J e)
  (hhf : ∀ v, 0 ≤ hf v)
  (hndE : ∀ e ∈ E, ¬ e.IsDiag)
  (hS₁ : S₁ ⊆ E)
  (hS₂ : S₂ ⊆ E)
  (hS₃ : S₃ ⊆ E)
  (h12 : Disjoint S₁ S₂)
  (h13 : Disjoint S₁ S₃)
  (h23 : Disjoint S₂ S₃) :
-- imply
  ghy_rho E J hf S₁ * ghy_rho E J hf S₂ * ghy_rho E J hf S₃ ≤ ghy_rho E J hf (S₁ ∪ S₂ ∪ S₃) := by
-- proof
  apply StatMech.Walls.ghy_rho_supermult_three E J hf hJ hhf hndE S₁ S₂ S₃ hS₁ hS₂ hS₃ h12 h13 h23


-- created on 2026-10-23
