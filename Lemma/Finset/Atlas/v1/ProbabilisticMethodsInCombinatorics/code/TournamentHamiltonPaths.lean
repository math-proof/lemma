import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.TournamentHamiltonPaths
open Real Finset BigOperators TournamentHamiltonPaths


namespace TournamentHamiltonPaths

/--
[numHamiltonPaths_le_factorial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamiltonPaths.lean)
-/
@[path]
lemma numHamiltonPaths_le_factorial
  {n : ℕ}
  {T : Tournament n} :
-- imply
  T.numHamiltonPaths ≤ n.factorial := by
-- proof
  classical
  unfold Tournament.numHamiltonPaths
  calc (Finset.univ.filter _).card
    ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = Fintype.card (Equiv.Perm (Fin n)) := rfl
    _ = n.factorial := by rw [Fintype.card_perm, Fintype.card_fin]

end TournamentHamiltonPaths

namespace TournamentHamiltonPaths

/--
[Tournament.adjMatrix_zero_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamiltonPaths.lean)
-/
@[path]
lemma Tournament.adjMatrix_zero_one
  {n : ℕ}
  {T : Tournament n} :
-- imply
  ∀ i j, T.adjMatrix i j = 0 ∨ T.adjMatrix i j = 1 := by
-- proof
  intro i j
  simp only [Tournament.adjMatrix, Matrix.of_apply]
  split_ifs <;> simp

end TournamentHamiltonPaths

namespace TournamentHamiltonPaths

/--
[successor_relation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamiltonPaths.lean)
-/
@[path]
lemma successor_relation
  {n : ℕ}
  {σ : Equiv.Perm (Fin (n + 1))}
  {j : Fin (n + 1)} :
-- imply
  σ (j + 1) = (toSuccPerm σ) (σ j) := by
-- proof
simp

end TournamentHamiltonPaths

namespace TournamentHamiltonPaths

/--
[toSuccPerm_valid](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamiltonPaths.lean)
-/
@[path]
lemma toSuccPerm_valid
  {n : ℕ}
  {T : Tournament (n + 1)}
  {σ : Equiv.Perm (Fin (n + 1))}
-- given
  (hσ : ∀ i : Fin (n + 1), T.edge (σ i) (σ (i + 1))) :
-- imply
  ∀ v : Fin (n + 1), T.edge v (toSuccPerm σ v) := by
-- proof
  intro v; simp only [toSuccPerm_apply]
  have h := hσ (σ⁻¹ v); convert h using 2; simp

end TournamentHamiltonPaths

namespace TournamentHamiltonPaths

/--
[fiber_eq_of_eq_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamiltonPaths.lean)
-/
@[path]
lemma fiber_eq_of_eq_at_zero
  {n : ℕ}
  {σ₁ σ₂ : Equiv.Perm (Fin (n + 1))}
-- given
  (heq : toSuccPerm σ₁ = toSuccPerm σ₂)
  (h0 : σ₁ 0 = σ₂ 0) :
-- imply
  σ₁ = σ₂ := by
-- proof
  set τ := toSuccPerm σ₁
  have h1 : ∀ j, σ₁ (j + 1) = τ (σ₁ j) := successor_relation σ₁
  have h2 : ∀ j, σ₂ (j + 1) = τ (σ₂ j) := by
    intro j; have := successor_relation σ₂ j; rw [← heq] at this; exact this
  apply Equiv.ext; intro ⟨i, hi⟩
  induction i with
  | zero => convert h0
  | succ k ih =>
    have hk : k < n + 1 := by omega
    have hfin : (⟨k + 1, hi⟩ : Fin (n + 1)) = (⟨k, hk⟩ : Fin (n + 1)) + 1 := by
      ext; show k + 1 = ((⟨k, hk⟩ : Fin (n + 1)) + 1).val
      simp [Fin.val_add, Nat.mod_eq_of_lt hi]
    rw [show σ₁ ⟨k + 1, hi⟩ = σ₁ ((⟨k, hk⟩ : Fin (n + 1)) + 1) from by rw [← hfin],
      show σ₂ ⟨k + 1, hi⟩ = σ₂ ((⟨k, hk⟩ : Fin (n + 1)) + 1) from by rw [← hfin],
      h1 ⟨k, hk⟩, h2 ⟨k, hk⟩, ih hk]

end TournamentHamiltonPaths

namespace TournamentHamiltonPaths

/--
[permanent_ge_card_row](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamiltonPaths.lean)
-/
@[path]
lemma permanent_ge_card_row
  {m : ℕ}
  {A : Matrix (Fin m) (Fin m) ℝ}
  {S : Finset (Equiv.Perm (Fin m))}
-- given
  (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
  (hS : ∀ σ ∈ S, ∀ i, A (σ i) i = 1) :
-- imply
  (S.card : ℝ) ≤ A.permanent := by
-- proof
  unfold Matrix.permanent
  calc (S.card : ℝ) = ∑ _ ∈ S, (1 : ℝ) := by rw [Finset.sum_const, Nat.smul_one_eq_cast]
    _ ≤ ∑ σ ∈ S, ∏ i : Fin m, A (σ i) i :=
      Finset.sum_le_sum (fun σ hσ => by rw [Finset.prod_eq_one (fun i _ => hS σ hσ i)])
    _ ≤ ∑ σ : Equiv.Perm (Fin m), ∏ i : Fin m, A (σ i) i :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun _ _ => Finset.mem_univ _)
        (fun σ _ _ => Finset.prod_nonneg
          (fun i _ => by rcases hA (σ i) i with h | h <;> linarith))

end TournamentHamiltonPaths

namespace TournamentHamiltonPaths

/--
[adjMatrix_entry_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamiltonPaths.lean)
-/
@[path]
lemma adjMatrix_entry_one_iff
  {m : ℕ}
  {T : Tournament m}
  {i j : Fin m} :
-- imply
  T.adjMatrix i j = 1 ↔ T.edge i j := by
-- proof
  simp only [Tournament.adjMatrix, Matrix.of_apply]; split_ifs with h <;> simp [h]

end TournamentHamiltonPaths

namespace TournamentHamiltonPaths

/--
[numHamiltonCycles_le_mul_permanent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamiltonPaths.lean)
-/
@[path]
lemma numHamiltonCycles_le_mul_permanent
  {n : ℕ}
  {T : Tournament (n + 1)} :
-- imply
  (T.numHamiltonCycles : ℝ) ≤ (n + 1) * T.adjMatrix.permanent := by
-- proof
  classical
  set S := Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
    ∀ i : Fin (n + 1), T.edge (σ i) (σ (i + 1)))
  have hnum : T.numHamiltonCycles = S.card := by
    unfold Tournament.numHamiltonCycles; rfl
  rw [hnum]
  have hS_prop : ∀ σ ∈ S, ∀ i : Fin (n + 1), T.edge (σ i) (σ (i + 1)) :=
    fun σ hσ => (Finset.mem_filter.mp hσ).2
  have h_fiber : ∀ τ ∈ Finset.image (toSuccPerm (n := n)) S,
    (S.filter (fun σ => toSuccPerm σ = τ)).card ≤ n + 1 := by
    intro τ _
    have hinj : Set.InjOn (fun σ : Equiv.Perm (Fin (n + 1)) => σ (0 : Fin (n + 1)))
      ↑(S.filter (fun σ => toSuccPerm σ = τ)) := by
      intro σ₁ hσ₁ σ₂ hσ₂ heq_val
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hσ₁ hσ₂
      exact fiber_eq_of_eq_at_zero σ₁ σ₂ (hσ₁.2.trans hσ₂.2.symm) heq_val
    calc (S.filter (fun σ => toSuccPerm σ = τ)).card
      ≤ (Finset.univ : Finset (Fin (n + 1))).card :=
        Finset.card_le_card_of_injOn (fun σ => σ 0) (fun _ _ => Finset.mem_univ _) hinj
      _ = n + 1 := Finset.card_fin _
  have h_bound : S.card ≤ (n + 1) * (Finset.image toSuccPerm S).card :=
    Finset.card_le_mul_card_image S (n + 1) h_fiber
  have h_image_valid : ∀ τ ∈ Finset.image (toSuccPerm (n := n)) S,
    ∀ v, T.adjMatrix v (τ v) = 1 := by
    intro τ hτ
    rw [Finset.mem_image] at hτ
    obtain ⟨σ, hσS, rfl⟩ := hτ
    intro v; rw [adjMatrix_entry_one_iff]
    exact toSuccPerm_valid T σ (hS_prop σ hσS) v
  let imgInv := (Finset.image toSuccPerm S).map
    ⟨fun σ => σ⁻¹, fun a b h => by simpa using congr_arg (·⁻¹) h⟩
  have h_imgInv_valid : ∀ σ ∈ imgInv, ∀ i, T.adjMatrix (σ i) i = 1 := by
    intro σ hσ
    simp only [imgInv, Finset.mem_map, Function.Embedding.coeFn_mk] at hσ
    obtain ⟨τ, hτ, rfl⟩ := hσ
    intro i; have := h_image_valid τ hτ (τ⁻¹ i); simp at this; exact this
  have h_imgInv_card : (Finset.image toSuccPerm S).card = imgInv.card := by simp [imgInv]
  have h_perm_ge : ((Finset.image toSuccPerm S).card : ℝ) ≤ T.adjMatrix.permanent := by
    rw [h_imgInv_card]
    exact permanent_ge_card_row T.adjMatrix T.adjMatrix_zero_one imgInv h_imgInv_valid
  have h_np1 : (↑(n + 1) : ℝ) = (↑n : ℝ) + 1 := by push_cast; ring
  calc (S.card : ℝ)
    ≤ ↑((n + 1) * (Finset.image toSuccPerm S).card) := by exact_mod_cast h_bound
    _ = (↑(n + 1) : ℝ) * ↑((Finset.image toSuccPerm S).card) := by push_cast; ring
    _ ≤ (↑(n + 1) : ℝ) * T.adjMatrix.permanent :=
      mul_le_mul_of_nonneg_left h_perm_ge (Nat.cast_nonneg' _)
    _ = ((↑n : ℝ) + 1) * T.adjMatrix.permanent := by rw [h_np1]
/-- Permanent optimization bound for tournament adjacency matrices: combining Brégman's
inequality with smoothing/Stirling, $(n + 1) \cdot \mathrm{perm}(A_T) \le
\sqrt{\pi/2 + 1} \cdot \sqrt{n+1} \cdot (n+1)! / 2^{n+1}$. -/

end TournamentHamiltonPaths


-- created on 2026-10-23
