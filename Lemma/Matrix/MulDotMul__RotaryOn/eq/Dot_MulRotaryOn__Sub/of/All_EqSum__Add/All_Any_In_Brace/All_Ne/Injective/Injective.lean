import Initialize.Tactic.Attr.Basic
import Lemma.Matrix.MulT_RotaryOn.eq.RotaryOn__Sub.of.All_EqSum__Add.All_OrAnyS_Eq.All_Ne.Injective.Injective
import Mathlib
open Matrix
open scoped Matrix


/--
Rotations on the same planes collapse to the relative angle under the dot product:
\((R_\alpha q) \cdot (R_\beta k) = q \cdot (R_{\beta - \alpha} k)\).
-/
@[path]
private lemma main
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (hu : Function.Injective u)
  (hv : Function.Injective v)
  (huv : ∀ t s, u t ≠ v s)
  (hsurj : ∀ i : Fin (d + d), ∃ t, i ∈ ({u t, v t} : Set (Fin (d + d))))
  (hsum : ∀ f : Fin (d + d) → ℝ, ∑ i, f i = ∑ t, f (u t) + ∑ t, f (v t))
  (α β : Fin d → ℝ)
  (q k : Fin (d + d) → ℝ) :
-- imply
  Matrix.rotaryOn u v α *ᵥ q ⬝ᵥ Matrix.rotaryOn u v β *ᵥ k =
    q ⬝ᵥ Matrix.rotaryOn u v (β - α) *ᵥ k := by
-- proof
  have hdisj : ∀ i : Fin (d + d), (∃ t, u t = i) ∨ (∃ t, v t = i) := by
    intro i
    obtain ⟨t, ht⟩ := hsurj i
    obtain h | h := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ht
    · exact Or.inl ⟨t, h.symm⟩
    · exact Or.inr ⟨t, h.symm⟩
  have hmul := MulT_RotaryOn.eq.RotaryOn__Sub.of.All_EqSum__Add.All_OrAnyS_Eq.All_Ne.Injective.Injective hu hv huv hdisj hsum α β
  rw [← hmul, ← Matrix.mulVec_mulVec, dotProduct_comm]
  exact (Matrix.dotProduct_transpose_mulVec (Matrix.rotaryOn u v α) q
    (Matrix.rotaryOn u v β *ᵥ k)).symm


-- created on 2026-11-27
