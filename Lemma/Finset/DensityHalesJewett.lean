import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.DensityHalesJewett
open scoped Finset
open Combinatorics.Line
open Combinatorics.Subspace
open MathlibExt.Combinatorics.DensityHalesJewettWanted


/--
[reindex_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DensityHalesJewett.lean)
-/
@[path]
private lemma reindex_apply_eq
  {l : Line α ι}
  {a : α}
  {i : ι'}
-- given
  (e : ι ≃ ι') :
-- imply
  l.reindex e a i = l a (e.symm i) := by
-- proof
  apply Combinatorics.Line.reindex_apply l e a i

/--
[comp_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DensityHalesJewett.lean)
-/
@[path]
private lemma comp_apply_eq
  {V : Subspace η α ι}
  {W : Subspace η' α η}
  {x : η' → α} :
-- imply
  V.comp W x = V (W x) := by
-- proof
  apply Combinatorics.Subspace.comp_apply V W x

/--
[compLine_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DensityHalesJewett.lean)
-/
@[path]
private lemma compLine_apply_eq
  {V : Subspace η α ι}
  {l : Combinatorics.Line α η}
  {a : α} :
-- imply
  V.compLine l a = V (l a) := by
-- proof
  apply Combinatorics.Subspace.compLine_apply V l a

/--
[reindex_compLine](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DensityHalesJewett.lean)
-/
@[path]
private lemma reindex_compLine_eq
  {V : Subspace η α ι}
  {l : Combinatorics.Line α η}
-- given
  (e : ι ≃ ι') :
-- imply
  (V.reindex (Equiv.refl η) (Equiv.refl α) e).compLine l = (V.compLine l).reindex e := by
-- proof
  apply Combinatorics.Subspace.reindex_compLine V e l

/--
[comp_compLine](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DensityHalesJewett.lean)
-/
@[path]
private lemma comp_compLine_eq
  {V : Subspace η α ι}
  {W : Subspace η' α η}
  {l : Combinatorics.Line α η'} :
-- imply
  (V.comp W).compLine l = V.compLine (W.compLine l) := by
-- proof
  apply Combinatorics.Subspace.comp_compLine V W l

/--
[_root_.Combinatorics.Subspace.exists_lines_mono_in_high_dimension_fin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DensityHalesJewett.lean)
-/
@[path]
private lemma Combinatorics_Subspace_exists_lines_mono_in_high_dimension_fin_eq
  {α : Type u} [Finite α] [Nonempty α]
  {κ : Type v} [Finite κ] [Nonempty κ]
  {m : ℕ} :
-- imply
  ∃ N : ℕ, ∀ C : Combinatorics.Line α (Fin N) → κ,
    ∃ V : Combinatorics.Subspace (Fin m) α (Fin N), ∃ z : κ,
    ∀ l : Combinatorics.Line α (Fin m), C (V.compLine l) = z := by
-- proof
  apply Combinatorics.Subspace.exists_lines_mono_in_high_dimension_fin α κ m

/--
[density_hales_jewett](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DensityHalesJewett.lean)
-/
@[path]
private lemma density_hales_jewett_eq
  :
-- imply
  ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ,
    ∀ A : Finset (Fin N → Fin k),
    δ * ((k : ℝ) ^ N) ≤ (A.card : ℝ) →
    ∃ l : Combinatorics.Line (Fin k) (Fin N), ∀ a : Fin k, l a ∈ A := by
-- proof
  apply MathlibExt.Combinatorics.DensityHalesJewettWanted.density_hales_jewett


-- created on 2026-10-20
