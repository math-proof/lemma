import Lemma.Finset.NotAny.is.All_Not
import Lemma.Finset.All.of.All.All_Imp
import Lemma.Finset.All_And.of.All.All
import Lemma.Bool.NotAny_Not.of.All
import Lemma.Nat.Eq.of.Le.Ge
open Bool Nat Finset


@[main]
private lemma main
  [AddCommMonoid N] [LinearOrder N] [IsOrderedAddMonoid N]
  {a : N}
  {x : ι → N}
  {s : Finset ι}
-- given
  (h₀ : ∀ i ∈ s, x i ≥ a)
  (h₁ : ∃ i ∈ s, x i ≠ a) :
-- imply
  ∃ i ∈ s, x i > a := by
-- proof
  by_contra h
  have h := All_Not.of.NotAny h
  have : ∀ t : N, ¬t > a → t ≤ a := by
    intro t h
    aesop
  have h_Ge_0 := All.of.All.All_Imp (α := N) this h
  have h := All_And.of.All.All h₀ h_Ge_0
  have : ∀ t : N, t ≥ a ∧ t ≤ a → t = a := by
    intro t ⟨h_ge, h_le⟩
    apply Eq.of.Le.Ge h_le h_ge
  have h := All.of.All.All_Imp this h
  have := NotAny_Not.of.All h
  have : ¬∃ i ∈ s, x i ≠ a := by
    simp
    simp at h
    exact h
  contradiction


-- created on 2025-04-06
-- updated on 2025-04-26
