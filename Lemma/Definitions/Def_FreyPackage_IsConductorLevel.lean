import Mathlib
import Lemma.Definitions.Def_FLTPrelim_FreyPackage

set_option autoImplicit false

namespace FreyPackage

structure IsConductorLevel (P : FreyPackage) (N : ℕ) : Prop where

  pos : 0 < N

  squarefree : Squarefree N

  support : ∀ q : ℕ, q.Prime → q ∣ N → (q : ℤ) ∣ P.a * P.b * P.c

namespace IsConductorLevel

variable {P : FreyPackage} {N : ℕ}

theorem of_dvd (h : P.IsConductorLevel N) {M : ℕ} (hMN : M ∣ N) (hM : 0 < M) :
    P.IsConductorLevel M :=
  ⟨hM, h.squarefree.squarefree_of_dvd hMN, fun q hq hqM => h.support q hq (hqM.trans hMN)⟩

theorem p_dvd_abc (h : P.IsConductorLevel N) (hpN : P.p ∣ N) :
    (P.p : ℤ) ∣ P.a * P.b * P.c :=
  h.support P.p P.pp hpN

theorem not_p_dvd (h : P.IsConductorLevel N) (hp : ¬ (P.p : ℤ) ∣ P.a * P.b * P.c) :
    ¬ P.p ∣ N :=
  fun hpN => hp (h.p_dvd_abc hpN)

theorem sq_not_dvd (h : P.IsConductorLevel N) {q : ℕ} (hq : q.Prime) : ¬ q ^ 2 ∣ N := by
  intro hsq
  exact Nat.squarefree_iff_prime_squarefree.mp h.squarefree q hq (by rwa [← pow_two])

theorem not_four_dvd (h : P.IsConductorLevel N) : ¬ 4 ∣ N := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  exact h4 ▸ h.sq_not_dvd Nat.prime_two

end IsConductorLevel

end FreyPackage
