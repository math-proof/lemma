import Mathlib
import sympy.Basic

open scoped IntermediateField Pointwise

/--
[IsPrimitiveRoot_existsUnique_eq_pow_val](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsPrimitiveRoot_existsUnique_eq_pow_val.lean)
-/
@[path]
private lemma main
  {R ι : Type*} [CommRing R] [IsDomain R]
  {ζ : Rˣ}
  {p : ℕ} [NeZero p]
  {f : ι → Rˣ}
-- given
  (hζ : IsPrimitiveRoot ζ p)
  (hf : ∀ i, f i ^ p = 1) :
-- imply
  ∃! c : ι → ZMod p, ∀ i, f i = ζ ^ (c i).val := by
-- proof
  have hex : ∀ i, ∃ k : ℕ, k < p ∧ ζ ^ k = f i := fun i =>
    hζ.eq_pow_of_mem_rootsOfUnity (by rw [mem_rootsOfUnity]; exact hf i)
  choose k hk hkf using hex
  refine ⟨fun i => (k i : ZMod p), fun i => ?_, fun c' hc' => ?_⟩
  · rw [ZMod.val_natCast_of_lt (hk i), hkf]
  · funext i
    have h := hc' i
    rw [← hkf i] at h
    have hv : (c' i).val = k i :=
      (hζ.pow_inj (ZMod.val_lt _) (hk i) h.symm)
    rw [← hv, ZMod.natCast_zmod_val]


-- created on 2026-10-05
