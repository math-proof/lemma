import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped BigOperators


namespace legendreSym

/--
[sum_linear_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LegendreSymbol/LinearSum.lean)
-/
@[path]
lemma sum_linear_eq_zero
  {p : ℕ} [Fact p.Prime]
  {b c : ℤ}
-- given
  (hpodd : Odd p)
  (hb : ¬ (p : ℤ) ∣ b) :
-- imply
  ∑ ℓ ∈ Finset.range p, legendreSym p (b * (ℓ : ℤ) + c) = 0 := by
-- proof
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have : NeZero p := ⟨hp0⟩
  have hb' : (b : ZMod p) ≠ 0 :=
    fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h)
  have hp2 : p ≠ 2 := hpodd.ne_two_of_dvd_nat (dvd_refl p)
  have hF : ringChar (ZMod p) ≠ 2 := by
    rwa [ZMod.ringChar_zmod_n]
  have hsum :
    (∑ x : ZMod p,
      quadraticChar (ZMod p) ((b : ZMod p) * x + (c : ZMod p))) = 0 := by
    calc
      _ = ∑ x : ZMod p, quadraticChar (ZMod p) x := by
        exact Fintype.sum_bijective
          (fun x : ZMod p ↦ (b : ZMod p) * x + (c : ZMod p))
          ((AddGroup.addRight_bijective (c : ZMod p)).comp
            (mulLeft_bijective₀ (b : ZMod p) hb')) _ _ (fun _ ↦ rfl)
      _ = 0 := quadraticChar_sum_zero hF
  have e_bij : Function.Bijective (fun i : Fin p => ((i.val : ℕ) : ZMod p)) := by
    constructor
    · intro a b hab
      have hmod : a.val ≡ b.val [MOD p] :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mp hab
      exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hmod a.isLt b.isLt)
    · intro x
      refine ⟨⟨x.val, ZMod.val_lt x⟩, ?_⟩
      change ((x.val : ℕ) : ZMod p) = x
      rw [ZMod.natCast_val, ZMod.cast_id]
  have hbridge := Function.Bijective.sum_comp e_bij
    (fun x : ZMod p => quadraticChar (ZMod p) ((b : ZMod p) * x + (c : ZMod p)))
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [legendreSym, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  simpa using hbridge.trans hsum

end legendreSym


-- created on 2026-10-20
-- updated on 2026-10-26
