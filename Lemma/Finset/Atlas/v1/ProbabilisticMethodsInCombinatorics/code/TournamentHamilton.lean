import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.TournamentHamilton.Part2
open TournamentHamilton


namespace TournamentHamilton

/--
[card_filter_two_constraints](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamilton.lean)
-/
@[path]
lemma card_filter_two_constraints
  {n : ℕ}
  {a b : Fin n}
-- given
  (hab : a ≠ b)
  (hn : n ≥ 2) :
-- imply
  (Finset.univ.filter (fun f : Fin n → Bool => f a = true ∧ f b = false)).card = 2 ^ (n - 2) := by
-- proof
  classical
  have h1 : (Finset.univ.filter (fun f : Fin n → Bool => f a = true ∧ f b = false)).card =
    Fintype.card {f : Fin n → Bool // f a = true ∧ f b = false} := by
    rw [Fintype.card_subtype]
  rw [h1]
  have h2 : Fintype.card {f : Fin n → Bool // f a = true ∧ f b = false} =
    Fintype.card ({i : Fin n // i ≠ a ∧ i ≠ b} → Bool) := by
    apply Fintype.card_of_bijective
    show Function.Bijective (fun (p : {f : Fin n → Bool // f a = true ∧ f b = false}) =>
      fun (i : {i : Fin n // i ≠ a ∧ i ≠ b}) => p.val i.val)
    constructor
    · intro ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ h
      simp only [Subtype.mk.injEq]
      ext i
      by_cases hia : i = a
      · subst hia; rw [hf₁.1, hf₂.1]
      · by_cases hib : i = b
        · subst hib; rw [hf₁.2, hf₂.2]
        · have := congr_fun h ⟨i, hia, hib⟩
          simpa using this
    · intro g
      refine ⟨⟨fun i => if h : i = a then true else if h2 : i = b then false else g ⟨i, h, h2⟩,
        ?_, ?_⟩, ?_⟩
      · simp
      · simp [hab.symm]
      · ext ⟨i, hi⟩; simp [hi.1, hi.2]
  rw [h2, Fintype.card_fun, Fintype.card_bool]
  congr 1
  rw [Fintype.card_subtype]
  have h_eq : (Finset.univ.filter (fun i : Fin n => i ≠ a ∧ i ≠ b)) =
    ((Finset.univ : Finset (Fin n)).erase a).erase b := by
    ext x; simp [Finset.mem_erase, ne_eq]; tauto
  rw [h_eq, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

end TournamentHamilton

namespace TournamentHamilton

/--
[card_good_orientations](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamilton.lean)
-/
@[path]
lemma card_good_orientations
  {n : ℕ}
  {σ : Equiv.Perm (Fin n)}
-- given
  (hn : n ≥ 2) :
-- imply
  (Finset.univ.filter (fun f : Fin n → Bool => f (σ ⟨0, by omega⟩) = true ∧ f (σ ⟨n - 1, by omega⟩) = false)).card = 2 ^ (n - 2) := by
-- proof
  apply card_filter_two_constraints
  · exact σ.injective.ne (by intro h; have := congrArg Fin.val h; simp at this; omega)
  · exact hn
/-- Injection from Hamilton paths compatible with $f$ into Hamilton cycles of the
extended tournament: each such path can be closed into a cycle via the new vertex. -/

end TournamentHamilton


-- created on 2026-10-23
