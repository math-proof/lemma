/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/DensityHalesJewett.lean -/


import sympy.atlas.Combinatorics.DensityHalesJewett
import Lemma.Finset.DensityHalesJewett

import Mathlib.Tactic.Ring


namespace MathlibExtTest.Combinatorics.DensityHalesJewett

universe u v

-- Reindexing sends every point of a covered line into the induced image.
example {α ι ι' : Type*} (l : Combinatorics.Line α ι) (e : ι ≃ ι')
    (A : Set (ι → α)) (hl : ∀ a, l a ∈ A) :
    ∀ a, l.reindex e a ∈ (fun x : ι → α => x ∘ e.symm) '' A := by
  intro a
  refine ⟨l a, hl a, ?_⟩
  funext i
  exact (Combinatorics.Line.reindex_apply l e a i).symm

-- Composing with an inner subspace preserves containment in the ambient point set.
example {η η' α ι : Type*} (V : Combinatorics.Subspace η α ι)
    (W : Combinatorics.Subspace η' α η) (A : Set (ι → α))
    (hV : ∀ x, V x ∈ A) : ∀ x, V.comp W x ∈ A := by
  intro x
  rw [Combinatorics.Subspace.comp_apply]
  exact hV (W x)

-- Transporting a line through a covered subspace keeps all line points covered.
example {η α ι : Type*} (V : Combinatorics.Subspace η α ι)
    (l : Combinatorics.Line α η) (A : Set (ι → α))
    (hV : ∀ x, V x ∈ A) : ∀ a, V.compLine l a ∈ A := by
  intro a
  rw [Combinatorics.Subspace.compLine_apply]
  exact hV (l a)

-- Constancy on all lines of a subspace descends to every composite subspace.
example {η η' α ι κ : Type*} (V : Combinatorics.Subspace η α ι)
    (W : Combinatorics.Subspace η' α η) (C : Combinatorics.Line α ι → κ)
    (hC : ∀ l₁ l₂ : Combinatorics.Line α η,
      C (V.compLine l₁) = C (V.compLine l₂)) :
    ∀ l₁ l₂ : Combinatorics.Line α η',
      C ((V.comp W).compLine l₁) = C ((V.comp W).compLine l₂) := by
  intro l₁ l₂
  simpa only [Combinatorics.Subspace.comp_compLine] using
    hC (W.compLine l₁) (W.compLine l₂)

-- Constancy on a subspace transfers to its reindexing under the induced coloring.
example {η α ι ι' κ : Type*} (V : Combinatorics.Subspace η α ι) (e : ι ≃ ι')
    (C : Combinatorics.Line α ι → κ)
    (hC : ∀ l₁ l₂ : Combinatorics.Line α η,
      C (V.compLine l₁) = C (V.compLine l₂)) :
    ∀ l₁ l₂ : Combinatorics.Line α η,
      C (((V.reindex (Equiv.refl η) (Equiv.refl α) e).compLine l₁).reindex e.symm) =
        C (((V.reindex (Equiv.refl η) (Equiv.refl α) e).compLine l₂).reindex e.symm) := by
  intro l₁ l₂
  have hroundtrip (l : Combinatorics.Line α ι) : (l.reindex e).reindex e.symm = l := by
    apply Combinatorics.Line.ext
    funext i
    simp [Combinatorics.Line.reindex]
  simpa only [Combinatorics.Subspace.reindex_compLine, hroundtrip] using hC l₁ l₂

-- A transported line in a concrete ternary square evaluates to the expected point.
example :
    let V : Combinatorics.Subspace (Fin 1) (Fin 3) (Fin 2) :=
      { idxFun := fun i => if i = 0 then Sum.inr 0 else Sum.inl 2
        proper := by decide }
    let l : Combinatorics.Line (Fin 3) (Fin 1) :=
      { idxFun := fun _ => none
        proper := ⟨0, rfl⟩ }
    V.compLine l 1 = fun i => if i = 0 then 1 else 2 := by
  dsimp only
  rw [Combinatorics.Subspace.compLine_apply]
  decide

-- Every half-dense ternary cube of a suitable dimension contains a line.
example : ∃ N : ℕ, ∀ A : Finset (Fin N → Fin 3),
    ((3 : ℝ) ^ N) / 2 ≤ (A.card : ℝ) →
      ∃ l : Combinatorics.Line (Fin 3) (Fin N), ∀ a : Fin 3, l a ∈ A := by
  obtain ⟨N, hN⟩ :=
    MathlibExt.Combinatorics.DensityHalesJewettWanted.density_hales_jewett
      3 (by omega) (1 / 2) (by norm_num)
  refine ⟨N, ?_⟩
  intro A hA
  apply hN A
  calc
    (1 / 2 : ℝ) * (3 : ℝ) ^ N = (3 : ℝ) ^ N / 2 := by ring
    _ ≤ (A.card : ℝ) := hA

-- Two-dimensional subspaces make every Boolean line-coloring constant on their lines.
example : ∃ N : ℕ, ∀ C : Combinatorics.Line (Fin 2) (Fin N) → Bool,
    ∃ V : Combinatorics.Subspace (Fin 2) (Fin 2) (Fin N),
      ∀ l₁ l₂ : Combinatorics.Line (Fin 2) (Fin 2),
        C (V.compLine l₁) = C (V.compLine l₂) := by
  obtain ⟨N, hN⟩ :=
    Combinatorics.Subspace.exists_lines_mono_in_high_dimension_fin (Fin 2) Bool 2
  refine ⟨N, ?_⟩
  intro C
  obtain ⟨V, z, hV⟩ := hN C
  exact ⟨V, fun l₁ l₂ => (hV l₁).trans (hV l₂).symm⟩

-- A universe-polymorphic line-coloring is constant on a one-dimensional subspace.
example {α : Type u} {κ : Type v} [Finite α] [Nonempty α] [Finite κ] [Nonempty κ] :
    ∃ N : ℕ, ∀ C : Combinatorics.Line α (Fin N) → κ,
      ∃ V : Combinatorics.Subspace (Fin 1) α (Fin N),
        ∃ l₀ : Combinatorics.Line α (Fin 1),
          ∀ l : Combinatorics.Line α (Fin 1), C (V.compLine l) = C (V.compLine l₀) := by
  let l₀ : Combinatorics.Line α (Fin 1) :=
    { idxFun := fun _ => none
      proper := ⟨0, rfl⟩ }
  obtain ⟨N, hN⟩ :=
    Combinatorics.Subspace.exists_lines_mono_in_high_dimension_fin α κ 1
  refine ⟨N, ?_⟩
  intro C
  obtain ⟨V, z, hV⟩ := hN C
  exact ⟨V, l₀, fun l => (hV l).trans (hV l₀).symm⟩

end MathlibExtTest.Combinatorics.DensityHalesJewett
