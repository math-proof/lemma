import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.FubiniNumber
import Lemma.Finset.Enumerative.FubiniNumber
import Lemma.Finset.Enumerative.SignedStirlingFirst
import Lemma.Finset.Enumerative.StirlingMatrices
import Def.Combinatorics.Enumerative.SignedStirlingFirst
import Def.Combinatorics.Enumerative.StirlingMatrices


namespace MetaMathlibExt

/--
[stirling_key](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FubiniRecurrence.lean)
-/
@[path]
private lemma stirling_key : ∀ (n : ℕ),
  ∑ i ∈ Finset.range (n + 1), signedStirlingFirst n i * (fubiniNumber i : ℤ) =
    (Nat.factorial n : ℤ) := by
  intro n
  have hfib : ∀ i ∈ Finset.range (n + 1), (fubiniNumber i : ℤ) =
    ∑ k ∈ Finset.range (i + 1), ((Nat.factorial k : ℤ) * (Nat.stirlingSecond i k : ℤ)) := by
    intro i _
    rw [fubiniNumber_eq_sum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.cast_mul, mul_comm]
  have hexpand : ∀ i ∈ Finset.range (n + 1),
    signedStirlingFirst n i * (fubiniNumber i : ℤ) =
      ∑ k ∈ Finset.range (n + 1),
        signedStirlingFirst n i * ((Nat.factorial k : ℤ) * (Nat.stirlingSecond i k : ℤ)) := by
    intro i hi
    have hsub : Finset.range (i + 1) ⊆ Finset.range (n + 1) := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      have hil : i < n + 1 := Finset.mem_range.mp hi
      omega
    have h0 : ∀ k ∈ Finset.range (n + 1), k ∉ Finset.range (i + 1) →
      signedStirlingFirst n i * ((Nat.factorial k : ℤ) * (Nat.stirlingSecond i k : ℤ)) = 0 := by
      intro k _ hk
      have hik : i < k := by
        simp only [Finset.mem_range, not_lt] at hk
        omega
      have hz : Nat.stirlingSecond i k = 0 := Nat.stirlingSecond_eq_zero_of_lt hik
      rw [hz]
      simp
    rw [hfib i hi, Finset.mul_sum]
    exact Finset.sum_subset hsub h0
  have hstep : (∑ i ∈ Finset.range (n + 1), signedStirlingFirst n i * (fubiniNumber i : ℤ)) =
    (∑ i ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
      signedStirlingFirst n i * ((Nat.factorial k : ℤ) * (Nat.stirlingSecond i k : ℤ))) :=
    Finset.sum_congr rfl (fun i hi => hexpand i hi)
  have hdouble : (∑ i ∈ Finset.range (n + 1), signedStirlingFirst n i * (fubiniNumber i : ℤ)) =
    (∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
      signedStirlingFirst n i * ((Nat.factorial k : ℤ) * (Nat.stirlingSecond i k : ℤ))) := by
    rwa [hstep]
  rw [hdouble]
  have hinner : ∀ k ∈ Finset.range (n + 1),
    (∑ i ∈ Finset.range (n + 1),
      signedStirlingFirst n i * ((Nat.factorial k : ℤ) * (Nat.stirlingSecond i k : ℤ))) =
      (Nat.factorial k : ℤ) * (if n = k then (1 : ℤ) else 0) := by
    intro k _
    calc (∑ i ∈ Finset.range (n + 1),
      signedStirlingFirst n i * ((Nat.factorial k : ℤ) * (Nat.stirlingSecond i k : ℤ)))
      = (Nat.factorial k : ℤ) *
        (∑ i ∈ Finset.range (n + 1),
          signedStirlingFirst n i * (Nat.stirlingSecond i k : ℤ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (Nat.factorial k : ℤ) * (if n = k then (1 : ℤ) else 0) := by
        rw [sum_signedStirlingFirst_mul_stirlingSecond n k]
  rw [Finset.sum_congr rfl (fun k hk => hinner k hk)]
  have hz : ∀ k ∈ Finset.range (n + 1), k ≠ n →
    (Nat.factorial k : ℤ) * (if n = k then (1 : ℤ) else 0) = 0 := by
    intro k _ hk
    rw [ite_eq_right (fun h : n = k => hk h.symm), mul_zero]
  have hn : n ∉ Finset.range (n + 1) →
    (Nat.factorial n : ℤ) * (if n = n then (1 : ℤ) else 0) = 0 := by
    intro h
    simp [Finset.mem_range] at h
  rw [Finset.sum_eq_single n hz hn, ite_eq_left rfl, mul_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fubiniNumber_eq_factorial_sub_sum_signed_stirling](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FubiniRecurrence.lean)
-/
@[path]
lemma fubiniNumber_eq_factorial_sub_sum_signed_stirling
  {n : ℕ} :
-- imply
  (fubiniNumber n : ℤ) =
    (Nat.factorial n : ℤ) -
    ∑ j ∈ Finset.Icc 1 n, signedStirlingFirst n (n - j) * (fubiniNumber (n - j) : ℤ) := by
-- proof
  have hkey := stirling_key n
  have hself : signedStirlingFirst n n = 1 := signedStirlingFirst_self n
  have hsplit : (∑ i ∈ Finset.range (n + 1), signedStirlingFirst n i * (fubiniNumber i : ℤ)) =
    (∑ i ∈ Finset.range n, signedStirlingFirst n i * (fubiniNumber i : ℤ)) +
      (fubiniNumber n : ℤ) := by
    have h' : (∑ i ∈ Finset.range (n + 1), signedStirlingFirst n i * (fubiniNumber i : ℤ)) =
      (∑ i ∈ Finset.range n, signedStirlingFirst n i * (fubiniNumber i : ℤ)) +
        signedStirlingFirst n n * (fubiniNumber n : ℤ) :=
      Finset.sum_range_succ _ n
    rw [h', hself, one_mul]
  have himg : Finset.image (fun j => n - j) (Finset.Icc 1 n) = Finset.range n := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      omega
    · intro h
      exact ⟨n - x, ⟨by omega, by omega⟩, by omega⟩
  have hinj : Set.InjOn (fun j => n - j) ↑(Finset.Icc 1 n) := by
    intro a ha b hb h
    have h' : n - a = n - b := h
    simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
    omega
  have hsum : (∑ i ∈ Finset.range n, signedStirlingFirst n i * (fubiniNumber i : ℤ)) =
    ∑ j ∈ Finset.Icc 1 n, signedStirlingFirst n (n - j) * (fubiniNumber (n - j) : ℤ) := by
    rw [← himg]
    exact Finset.sum_image hinj
  have hcomb : (Nat.factorial n : ℤ) =
    (∑ j ∈ Finset.Icc 1 n, signedStirlingFirst n (n - j) * (fubiniNumber (n - j) : ℤ)) +
      (fubiniNumber n : ℤ) := by
    rw [← hsum, ← hsplit, hkey]
  rw [hcomb]
  ring

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
