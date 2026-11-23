import Lemma.Fin.RopeEven.ne.RopeOdd
import Lemma.Fin.Any_In_BraceRopeEven__RopeOdd
import Lemma.Fin.InjectiveRopeEven
import Lemma.Fin.InjectiveRopeOdd
import Lemma.Matrix.InvRotaryOn.eq.TRotaryOn.of.All_EqSum__Add.All_OrAnyS_Eq.All_Ne.Injective.Injective
import Lemma.Real.Sum.eq.AddSumS
import Mathlib
open Fin Matrix Real
open scoped Matrix


/-- The interleaved rotary matrix is invertible with inverse its transpose. -/
@[path]
private lemma main
  {d : ℕ}
-- given
  (φ : Fin d → ℝ) :
-- imply
  (Matrix.rotary' φ)⁻¹ = (Matrix.rotary' φ)ᵀ := by
-- proof
  simpa [Matrix.rotary'] using
    InvRotaryOn.eq.TRotaryOn.of.All_EqSum__Add.All_OrAnyS_Eq.All_Ne.Injective.Injective
      (InjectiveRopeEven d) (InjectiveRopeOdd d) (RopeEven.ne.RopeOdd d)
      (fun i => by
        obtain ⟨t, ht⟩ := Any_In_BraceRopeEven__RopeOdd d i
        obtain h | h := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ht
        · exact Or.inl ⟨t, h.symm⟩
        · exact Or.inr ⟨t, h.symm⟩)
      (Sum.eq.AddSumS d) φ


-- created on 2026-11-23
