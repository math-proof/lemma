import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.Padics.Polynomial
open Polynomial


namespace Polynomial

/--
[padicValuation_le_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Polynomial.lean)
-/
@[path]
lemma padicValuation_le_coeff
  {p : ℕ}
  {hp : Nat.Prime p}
  {f : Polynomial ℤ}
  {hf : f ≠ 0}
  {n : ℕ}
-- given
  (hn : n ∈ f.support) :
-- imply
  padicValuation p hp f hf ≤ padicValInt p (f.coeff n) := by
-- proof
  unfold padicValuation
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem (fun n => padicValInt p (f.coeff n)) hn)

end Polynomial

namespace Polynomial

/--
[le_padicValuation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Polynomial.lean)
-/
@[path]
lemma le_padicValuation
  {p : ℕ}
  {hp : Nat.Prime p}
  {f : Polynomial ℤ}
  {hf : f ≠ 0}
  {k : ℕ}
-- given
  (hk : ∀ n ∈ f.support, k ≤ padicValInt p (f.coeff n)) :
-- imply
  k ≤ padicValuation p hp f hf := by
-- proof
  unfold padicValuation
  apply Finset.le_min'
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨n, hn, rfl⟩ := hy
  exact hk n hn

end Polynomial

namespace Polynomial

/--
[padicValuation_C](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Polynomial.lean)
-/
@[path]
lemma padicValuation_C
  {p : ℕ}
  {a : ℤ}
-- given
  (hp : Nat.Prime p)
  (ha : a ≠ 0) :
-- imply
  padicValuation p hp (C a) (C_ne_zero.mpr ha) = padicValInt p a := by
-- proof
  apply le_antisymm
  · have h0 : 0 ∈ (C a : Polynomial ℤ).support := by
    rw [support_C ha]
    exact Finset.mem_singleton_self 0
    calc
      padicValuation p hp (C a) (C_ne_zero.mpr ha) ≤ padicValInt p ((C a).coeff 0) :=
        padicValuation_le_coeff h0
      _ = padicValInt p a := by rw [coeff_C_zero]
  · apply le_padicValuation
    intro n hn
    rw [support_C ha] at hn
    rw [Finset.mem_singleton.mp hn, coeff_C_zero]

end Polynomial


-- created on 2026-10-20
-- updated on 2026-10-26
