import Mathlib
import sympy.Basic
import sympy.atlas.Data.Set.Density
open Filter
open scoped Topology
open Set
open Finset Real
open HasIntDensity
open HasDensity
open Nat


/--
[partialDensity_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
private lemma partialDensity_le_one_eq
  :
-- imply
  {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := by
-- proof
  apply Set.partialDensity_le_one

/--
[lowerDensity_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
private lemma lowerDensity_le_one_eq
  :
-- imply
  {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := by
-- proof
  apply Set.lowerDensity_le_one

/--
[lowerDensity_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
private lemma lowerDensity_nonneg_eq
  :
-- imply
  {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := by
-- proof
  apply Set.lowerDensity_nonneg

/--
[intPartialDensity_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
private lemma intPartialDensity_empty_eq
  {N : ℕ} :
-- imply
  intPartialDensity (∅ : Set ℤ) N = 0 := by
-- proof
  apply Set.intPartialDensity_empty N

/--
[empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
private lemma empty_eq
  :
-- imply
  HasIntDensity (∅ : Set ℤ) 0 := by
-- proof
  apply Set.HasIntDensity.empty

/--
[univ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
private lemma univ_eq
  [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β] [Nontrivial β] :
-- imply
  (@univ β).HasDensity 1 := by
-- proof
  apply Set.HasDensity.univ

/--
[univ_nat_hasDensity_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
private lemma univ_nat_hasDensity_one_eq
  :
-- imply
  (@univ ℕ).HasDensity 1 := by
-- proof
  apply Set.HasDensity.univ_nat_hasDensity_one

/--
[empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
private lemma Set_HasDensity_empty_eq
  :
-- imply
  HasIntDensity (∅ : Set ℤ) 0 := by
-- proof
  apply Set.HasDensity.empty

/--
[mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
private lemma mono_eq
  :
-- imply
  {β : Type*} [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β]
    {S T : Set β} {αS αT : ℝ} [(atTop (α := by
-- proof
  apply Set.HasDensity.mono

/--
[nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
private lemma nonneg_eq
  [Preorder β] [LocallyFiniteOrderBot β] [(atTop : Filter β).NeBot]
  {S : Set β}
  {α : ℝ}
-- given
  (h : S.HasDensity α) :
-- imply
  0 ≤ α := by
-- proof
  apply Set.HasDensity.nonneg h

/--
[hasDensity_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
private lemma hasDensity_even_eq
  :
-- imply
  {n : ℕ | Even n}.HasDensity (1 / 2) := by
-- proof
  apply Set.Nat.hasDensity_even

/--
[hasDensity_zero_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
private lemma hasDensity_zero_of_finite_eq
  {S : Set ℕ}
-- given
  (h : S.Finite) :
-- imply
  S.HasDensity 0 := by
-- proof
  apply Set.Nat.hasDensity_zero_of_finite h

/--
[infinite_of_hasDensity_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
private lemma infinite_of_hasDensity_pos_eq
  {S : Set ℕ}
  {α : ℝ}
-- given
  (h : S.HasDensity α)
  (hα : α ≠ 0) :
-- imply
  S.Infinite := by
-- proof
  apply Set.Nat.infinite_of_hasDensity_pos h hα


-- created on 2026-10-20
