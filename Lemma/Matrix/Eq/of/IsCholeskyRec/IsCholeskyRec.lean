import Def.Analysis.Matrix.Cholesky
import Initialize.Tactic.Attr.Basic
open scoped ComplexOrder


@[path]
private lemma main
  [RCLike 𝕜]
  {n : ℕ}
  {A L M : Matrix (Fin n) (Fin n) 𝕜}
-- given
  (h₁ : IsCholeskyRec A L)
  (h₂ : IsCholeskyRec A M) :
-- imply
  L = M := by
-- proof
  have key : ∀ j, ∀ i, L i j = M i j := by
    intro j
    induction j using WellFoundedLT.induction with
    | _ j ih =>
      have hdiag : L j j = M j j := by
        have hs : ∑ k ∈ Finset.Iio j, ‖L j k‖ ^ 2 = ∑ k ∈ Finset.Iio j, ‖M j k‖ ^ 2 :=
          Finset.sum_congr rfl fun k hk => by rw [ih k (Finset.mem_Iio.mp hk) j]
        rw [h₁ j j, h₂ j j, ite_eq_right (lt_irrefl j), ite_eq_left rfl, ite_eq_right (lt_irrefl j), ite_eq_left rfl, hs]
      intro i
      obtain h | rfl | h := lt_trichotomy j i
      ·
        have hs : ∑ k ∈ Finset.Iio j, L i k * star (L j k) = ∑ k ∈ Finset.Iio j, M i k * star (M j k) :=
          Finset.sum_congr rfl fun k hk => by rw [ih k (Finset.mem_Iio.mp hk) i, ih k (Finset.mem_Iio.mp hk) j]
        rw [h₁ i j, h₂ i j, ite_eq_left h, ite_eq_left h, hs, hdiag]
      · exact hdiag
      · rw [h₁ i j, h₂ i j, ite_eq_right (not_lt.mpr h.le), ite_eq_right h.ne', ite_eq_right (not_lt.mpr h.le), ite_eq_right h.ne']
  ext i j
  exact key j i


-- created on 2026-10-07
