import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.LieGroups.code.CoxeterTheory.Part2
open CoxeterGroupData
open scoped BigOperators


namespace Definitions
end Definitions
namespace CoxeterGroupData

/--
[descentRefl_length_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CoxeterTheory.lean)
-/
@[path]
private lemma descentRefl_length_eq
  {C : CoxeterGroupData}
  {y : C.W}
-- given
  (hy : y ≠ 1) :
-- imply
  C.length (C.descentRefl y * y) + 1 = C.length y := by
-- proof
  have hs := C.descentRefl_simple y hy
  have hlt := C.descentRefl_length y hy
  have hex := C.exchange_left (C.descentRefl y) hs y
  omega

end CoxeterGroupData

namespace CoxeterGroupData

/--
[length_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CoxeterTheory.lean)
-/
@[path]
private lemma length_mul_le
  {C : CoxeterGroupData}
  {v w : C.W} :
-- imply
  C.length (v * w) ≤ C.length v + C.length w := by
-- proof
  suffices h : ∀ (n : ℕ) (v w : C.W), C.length v = n →
    C.length (v * w) ≤ C.length v + C.length w from
    h (C.length v) v w rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro v w hv
    by_cases hv1 : v = 1
    · subst hv1; simp only [one_mul]; omega
    · set s := C.descentRefl v with s_def
      have hs := C.descentRefl_simple v hv1
      have hlen_v : C.length (s * v) + 1 = C.length v :=
        C.descentRefl_length_eq v hv1
      have hsq : s * s = 1 := C.simple_sq s hs
      have hv_eq : v = s * (s * v) := by
        calc v = 1 * v := by rw [one_mul]
          _ = (s * s) * v := by rw [hsq]
          _ = s * (s * v) := by rw [mul_assoc]
      have hvw_eq : v * w = s * ((s * v) * w) := by
        conv_lhs => rw [hv_eq]
        rw [mul_assoc]
      have hex := C.exchange_left s hs ((s * v) * w)
      have hlen_sv_lt : C.length (s * v) < n := by omega
      have ih_app := ih (C.length (s * v)) hlen_sv_lt (s * v) w rfl
      rw [hvw_eq]
      omega

end CoxeterGroupData

namespace CoxeterGroupData

/--
[length_inv_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CoxeterTheory.lean)
-/
@[path]
private lemma length_inv_le
  {C : CoxeterGroupData}
  {w : C.W} :
-- imply
  C.length w⁻¹ ≤ C.length w := by
-- proof
  suffices h : ∀ (n : ℕ) (w : C.W), C.length w = n → C.length w⁻¹ ≤ C.length w from
    h (C.length w) w rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro w hw
    by_cases hw1 : w = 1
    · subst hw1; simp [inv_one]
    · set s := C.descentRefl w with s_def
      have hs := C.descentRefl_simple w hw1
      have hlen : C.length (s * w) + 1 = C.length w := C.descentRefl_length_eq w hw1
      have hsq : s * s = 1 := C.simple_sq s hs
      have hs_inv : s⁻¹ = s := by
        rw [inv_eq_of_mul_eq_one_right hsq]
      have hw_eq : w = s * (s * w) := by
        calc w = 1 * w := by rw [one_mul]
          _ = (s * s) * w := by rw [hsq]
          _ = s * (s * w) := by rw [mul_assoc]
      have hinv_eq : w⁻¹ = (s * w)⁻¹ * s := by
        conv_lhs => rw [hw_eq]
        rw [mul_inv_rev, hs_inv]
      have h1 : C.length w⁻¹ ≤ C.length (s * w)⁻¹ + C.length s := by
        rw [hinv_eq]; exact C.length_mul_le (s * w)⁻¹ s
      have h2 : C.length s = 1 := C.length_simple s hs
      have hlen_lt : C.length (s * w) < n := by omega
      have h3 : C.length (s * w)⁻¹ ≤ C.length (s * w) :=
        ih (C.length (s * w)) hlen_lt (s * w) rfl
      omega
end CoxeterGroupData
namespace WeylGroupData


-- created on 2026-10-24
-- updated on 2026-10-28
