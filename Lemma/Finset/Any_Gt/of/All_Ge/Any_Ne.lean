import Lemma.Bool.NotAny.is.All_Not
import Lemma.Bool.All.of.All.All_Imp
import Lemma.Bool.All_And.of.All.All
import Lemma.Bool.NotAny_Not.of.All
import Lemma.Nat.Eq.of.Le.Ge
open Bool Nat


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
  have h := All_Not.of.NotAny.fin h
  have : ∀ t : N, ¬t > a → t ≤ a := by
    intro t h
    aesop
  have h_Ge_0 := All.of.All.All_Imp.fin (α := N) this h
  have h := All_And.of.All.All.fin h₀ h_Ge_0
  have : ∀ t : N, t ≥ a ∧ t ≤ a → t = a := by
    intro t ⟨h_ge, h_le⟩
    apply Eq.of.Le.Ge h_le h_ge
  have h := All.of.All.All_Imp.fin this h
  have := NotAny_Not.of.All h
  have h_NotAny : ¬∃ i ∈ s, x i ≠ a := by
    simp
    simp at h
    exact h
  contradiction


-- created on 2025-04-06
-- updated on 2025-04-26
