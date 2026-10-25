import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.SzemerediTrotterProjection
open Finset Real Set SzemerediTrotterProjection
open Classical


namespace SzemerediTrotterProjection

/--
[st_fiber_incidence_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotterProjection.lean)
-/
@[path]
lemma st_fiber_incidence_bound
  {X : Finset (ℝ × ℝ)}
  {S : ℕ}
  {n : ℕ}
-- given
  (hn : n = (smallProjDirections X S).ncard)
  (hfin : (smallProjDirections X S).Finite)
  (hSlt : S < X.card)
  (hn2 : n ≥ 2) :
-- imply
  (n : ℝ) * (X.card : ℝ) ≤ (X.card : ℝ) + (n : ℝ) * (S : ℝ) + (X.card : ℝ) ^ ((2 : ℝ) / 3) * ((n : ℝ) * (S : ℝ)) ^ ((2 : ℝ) / 3) := by
-- proof
  classical
  let toFin2 : ℝ × ℝ → (Fin 2 → ℝ) := fun p => ![p.1, p.2]
  have toFin2_inj : Function.Injective toFin2 := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    simp only [toFin2] at h
    have h0 : (![a₁, b₁] : Fin 2 → ℝ) 0 = (![a₂, b₂] : Fin 2 → ℝ) 0 := congr_fun h 0
    have h1 : (![a₁, b₁] : Fin 2 → ℝ) 1 = (![a₂, b₂] : Fin 2 → ℝ) 1 := congr_fun h 1
    simp [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact Prod.ext h0 h1
  let X' : Finset (Fin 2 → ℝ) := X.image toFin2
  have hX'card : X'.card = X.card := Finset.card_image_of_injective X toFin2_inj
  have hXne : X.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero (by omega))
  have hX'ne : X'.Nonempty := Finset.image_nonempty.mpr hXne
  let D : Finset ℝ := hfin.toFinset
  have hDcard : D.card = n := by
    rw [hn]
    exact (Set.ncard_eq_toFinset_card (smallProjDirections X S) hfin).symm
  have hDr : ∀ θ ∈ D, 0 ≤ θ ∧ θ < Real.pi := by
    intro θ hθ
    have hmem := hfin.mem_toFinset.mp hθ
    exact hmem.1
  have proj_eq : ∀ θ (p : ℝ × ℝ), ProjectionTheory.projR2 θ (toFin2 p) = orthProj θ p := by
    intro θ ⟨a, b⟩
    simp [ProjectionTheory.projR2, toFin2, orthProj, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  have projImg_eq : ∀ θ, ProjectionTheory.projImageR2 θ X' = projImage θ X := by
    intro θ
    simp only [ProjectionTheory.projImageR2, projImage, X']
    rw [Finset.image_image]
    exact Finset.image_congr (fun p _ => proj_eq θ p)
  have hSb : ∀ θ ∈ D, (ProjectionTheory.projImageR2 θ X').card ≤ S := by
    intro θ hθ
    rw [projImg_eq]
    have hmem := hfin.mem_toFinset.mp hθ
    exact hmem.2
  obtain ⟨L, hLcard, hIncid⟩ := ProjectionTheory.fiber_lines_st_bound X' S D hDr hSb hX'ne
  have hST := SzemerediTrotter.szemeredi_trotter X' L
  have hIncid_r : (X.card : ℝ) * (n : ℝ) ≤ (SzemerediTrotter.incidenceCount X' L : ℝ) := by
    have h1 : X'.card * D.card ≤ SzemerediTrotter.incidenceCount X' L := hIncid
    rw [hX'card, hDcard] at h1
    exact_mod_cast h1
  rw [hX'card] at hST
  have hLcard_r : (L.card : ℝ) ≤ (n : ℝ) * (S : ℝ) := by
    have h1 : L.card ≤ S * D.card := hLcard
    rw [hDcard] at h1
    have h2 : L.card ≤ n * S := Nat.mul_comm S n ▸ h1
    exact_mod_cast h2
  calc (n : ℝ) * (X.card : ℝ)
    = (X.card : ℝ) * (n : ℝ) := by ring
    _ ≤ (SzemerediTrotter.incidenceCount X' L : ℝ) := hIncid_r
    _ ≤ (X.card : ℝ) + (L.card : ℝ) +
      (X.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) := hST
    _ ≤ (X.card : ℝ) + (n : ℝ) * (S : ℝ) +
      (X.card : ℝ) ^ ((2 : ℝ) / 3) * ((n : ℝ) * (S : ℝ)) ^ ((2 : ℝ) / 3) := by
      gcongr
/-- Algebraic lemma extracting the projection bound $n \le S^2/P + 1$ from the
Szemerédi--Trotter incidence inequality $nP \le P + nS + P^{2/3}(nS)^{2/3}$. -/
end SzemerediTrotterProjection
namespace SzemerediTrotter
open Classical
/-- **Beck's theorem / Szemerédi--Trotter lower bound on lines.** There exists a constant
$C > 0$ such that for any finite point set $E \subset \mathbb{R}^2$ and any choice of
$S$ lines through each point $x \in E$, the union
$L = \bigcup_{x \in E} L_x$ has size
$|L| \gtrsim \min(|E| \cdot S, |E|^{1/2} S^{3/2})$. -/
end SzemerediTrotter



-- created on 2026-10-23
