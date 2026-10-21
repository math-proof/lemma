import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma finite_of_krullDim_lt_top (P : Type*) [LinearOrder P] (h : Order.krullDim P < ⊤) :
    Finite P := by
  by_contra hinf
  rw [not_finite_iff_infinite] at hinf
  have hn : ∀ n : ℕ, (n : WithBot ℕ∞) ≤ Order.krullDim P := by
    intro n
    rw [Order.le_krullDim_iff]
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq P (n + 1)
    refine ⟨⟨n, fun i => s.orderEmbOfFin hs i, fun i => ?_⟩, rfl⟩
    exact (s.orderEmbOfFin hs).strictMono (Fin.castSucc_lt_succ)
  have htop : Order.krullDim P = ⊤ := by
    have hne : Order.krullDim P ≠ ⊥ := Order.krullDim_ne_bot_iff.mpr inferInstance
    obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
    rw [← hd] at hn ⊢
    have hd' : d = ⊤ := ENat.eq_top_iff_forall_ge.mpr (fun m => by exact_mod_cast hn m)
    rw [hd']; rfl
  exact h.ne htop
/--
[ValuationSubring_finite_primeSpectrum_of_ringKrullDim_lt_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_finite_primeSpectrum_of_ringKrullDim_lt_top.lean)
-/
@[path]
private lemma main {L : Type*} [Field L] (A : ValuationSubring L) (h : ringKrullDim A < ⊤) :
    Finite (PrimeSpectrum A) := by
  have e := ValuationSubring.primeSpectrumOrderEquiv A
  have hdim : Order.krullDim {S // A ≤ S} < ⊤ := by
    rw [← Order.krullDim_eq_of_orderIso e, Order.krullDim_orderDual]; exact h
  have hfin : Finite {S // A ≤ S} := finite_of_krullDim_lt_top _ hdim
  exact Finite.of_equiv _ e.toEquiv.symm

-- created on 2026-10-20
