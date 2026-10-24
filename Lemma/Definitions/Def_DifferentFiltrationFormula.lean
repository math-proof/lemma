import Lemma.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup
import Mathlib.RingTheory.DedekindDomain.Different

set_option autoImplicit false

open scoped Pointwise

attribute [local instance] FractionRing.liftAlgebra

section FiltrationSum

variable (B : Type*) [CommRing B] [IsLocalRing B]
variable (G : Type*) [Group G] [MulSemiringAction G B]

noncomputable def lowerRamificationFiltrationSum (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range N, (Nat.card (IsLocalRing.lowerRamificationGroup B G i) - 1)

noncomputable def lowerRamificationDepthCount (N : ℕ) (σ : G) : ℕ :=
  letI : DecidablePred fun i => σ ∈ IsLocalRing.lowerRamificationGroup B G i :=
    fun _ => Classical.propDecidable _
  ((Finset.range N).filter fun i => σ ∈ IsLocalRing.lowerRamificationGroup B G i).card

variable {B G}

theorem lowerRamificationGroup_eq_bot_of_le {N M : ℕ}
    (hN : IsLocalRing.lowerRamificationGroup B G N = ⊥) (hNM : N ≤ M) :
    IsLocalRing.lowerRamificationGroup B G M = ⊥ :=
  le_bot_iff.mp (hN ▸ IsLocalRing.lowerRamificationGroup_antitone hNM)

theorem lowerRamificationFiltrationSum_eq_of_le {N M : ℕ}
    (hN : IsLocalRing.lowerRamificationGroup B G N = ⊥) (hNM : N ≤ M) :
    lowerRamificationFiltrationSum B G M = lowerRamificationFiltrationSum B G N := by
  unfold lowerRamificationFiltrationSum
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le N) hNM,
    ← Finset.range_eq_Ico]
  have h0 : ∀ i ∈ Finset.Ico N M,
      Nat.card (IsLocalRing.lowerRamificationGroup B G i) - 1 = 0 := by
    intro i hi
    rw [lowerRamificationGroup_eq_bot_of_le hN (Finset.mem_Ico.mp hi).1, Subgroup.card_bot]
  rw [Finset.sum_eq_zero h0, add_zero]

theorem lowerRamificationFiltrationSum_eq_of_eq_bot {N M : ℕ}
    (hN : IsLocalRing.lowerRamificationGroup B G N = ⊥)
    (hM : IsLocalRing.lowerRamificationGroup B G M = ⊥) :
    lowerRamificationFiltrationSum B G N = lowerRamificationFiltrationSum B G M := by
  rcases le_total N M with h | h
  · exact (lowerRamificationFiltrationSum_eq_of_le hN h).symm
  · exact lowerRamificationFiltrationSum_eq_of_le hM h

private theorem sum_erase_one_ite_mem [Fintype G] [DecidableEq G] (H : Subgroup G)
    [DecidablePred (· ∈ H)] :
    (∑ σ ∈ Finset.univ.erase (1 : G), if σ ∈ H then 1 else 0) = Nat.card H - 1 := by
  classical
  rw [← Finset.card_filter, Finset.filter_erase,
    Finset.card_erase_of_mem (by simp [H.one_mem]), Nat.card_eq_fintype_card,
    Fintype.card_subtype]

theorem sum_lowerRamificationDepthCount_erase_one [Fintype G] [DecidableEq G] (N : ℕ) :
    (∑ σ ∈ Finset.univ.erase (1 : G), lowerRamificationDepthCount B G N σ)
      = lowerRamificationFiltrationSum B G N := by
  classical
  simp only [lowerRamificationDepthCount, lowerRamificationFiltrationSum, Finset.card_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ =>
    sum_erase_one_ite_mem (IsLocalRing.lowerRamificationGroup B G i)

end FiltrationSum

section StatementLayer

variable (A : Type*) [CommRing A] [IsDomain A]
variable (B : Type*) [CommRing B] [IsDedekindDomain B] [IsLocalRing B]
variable [Algebra A B] [Module.IsTorsionFree A B]
variable (G : Type*) [Group G] [MulSemiringAction G B]

def DifferentEqPowFiltrationSum : Prop :=
  ∀ N : ℕ, IsLocalRing.lowerRamificationGroup B G N = ⊥ →
    differentIdeal A B
      = IsLocalRing.maximalIdeal B ^ lowerRamificationFiltrationSum B G N

variable {A B G}

theorem differentEqPowFiltrationSum_of_cutoff {N : ℕ}
    (hN : IsLocalRing.lowerRamificationGroup B G N = ⊥)
    (h : differentIdeal A B
      = IsLocalRing.maximalIdeal B ^ lowerRamificationFiltrationSum B G N) :
    DifferentEqPowFiltrationSum A B G := by
  intro M hM
  rw [h, lowerRamificationFiltrationSum_eq_of_eq_bot hN hM]

end StatementLayer
