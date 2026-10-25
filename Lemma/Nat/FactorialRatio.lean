import Mathlib
import sympy.Basic
import Def.NumberTheory.FactorialRatio


/--
[factorialProd_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma factorialProd_nil
  {n : ℕ} :
-- imply
  factorialProd [] n = 1 :=
-- proof
  rfl

/--
[factorialProd_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma factorialProd_cons
  {a : ℕ}
  {L : List ℕ}
  {n : ℕ} :
-- imply
  factorialProd (a :: L) n =
    Nat.factorial (a * n) * factorialProd L n :=
-- proof
  rfl

/--
[factorialProd_perm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma factorialProd_perm
  {L₁ L₂ : List ℕ}
  {n : ℕ}
-- given
  (h : List.Perm L₁ L₂) :
-- imply
  factorialProd L₁ n = factorialProd L₂ n := by
-- proof
  unfold factorialProd
  exact (h.map _).prod_eq

/--
[factorialProd_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma factorialProd_zero
  {L : List ℕ} :
-- imply
  factorialProd L 0 = 1 := by
-- proof
  unfold factorialProd
  apply List.prod_eq_one
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  rw [Nat.mul_zero, Nat.factorial_zero]

/--
[factorialProd_dvd_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma factorialProd_dvd_zero
  {A B : List ℕ} :
-- imply
  factorialProd B 0 ∣ factorialProd A 0 := by
-- proof
  rw [factorialProd_zero, factorialProd_zero]

/--
[isIntegralFactorialRatio_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma isIntegralFactorialRatio_iff
  {A B : List ℕ} :
-- imply
  IsIntegralFactorialRatio A B ↔
    (∀ a ∈ A, 0 < a) ∧ (∀ b ∈ B, 0 < b) ∧ A.sum = B.sum ∧
    ∀ n : ℕ, factorialProd B n ∣ factorialProd A n :=
-- proof
  Iff.rfl

/--
[IsIntegralFactorialRatio.pos_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma IsIntegralFactorialRatio.pos_left
  {A B : List ℕ}
-- given
  (h : IsIntegralFactorialRatio A B) :
-- imply
  ∀ a ∈ A, 0 < a :=
-- proof
  h.1

/--
[IsIntegralFactorialRatio.pos_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma IsIntegralFactorialRatio.pos_right
  {A B : List ℕ}
-- given
  (h : IsIntegralFactorialRatio A B) :
-- imply
  ∀ b ∈ B, 0 < b :=
-- proof
  h.2.1

/--
[IsIntegralFactorialRatio.sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma IsIntegralFactorialRatio.sum_eq
  {A B : List ℕ}
-- given
  (h : IsIntegralFactorialRatio A B) :
-- imply
  A.sum = B.sum :=
-- proof
  h.2.2.1

/--
[IsIntegralFactorialRatio.dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma IsIntegralFactorialRatio.dvd
  {A B : List ℕ}
  {n : ℕ}
-- given
  (h : IsIntegralFactorialRatio A B) :
-- imply
  factorialProd B n ∣ factorialProd A n :=
-- proof
  h.2.2.2 n

/--
[IsIntegralFactorialRatio.mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma IsIntegralFactorialRatio.mk
  {A B : List ℕ}
-- given
  (hA : ∀ a ∈ A, 0 < a)
  (hB : ∀ b ∈ B, 0 < b)
  (hsum : A.sum = B.sum)
  (hdvd : ∀ n : ℕ, factorialProd B n ∣ factorialProd A n) :
-- imply
  IsIntegralFactorialRatio A B :=
-- proof
  ⟨hA, hB, hsum, hdvd⟩

/--
[isIntegralFactorialRatio_perm_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma isIntegralFactorialRatio_perm_left
  {A A' B : List ℕ}
-- given
  (hperm : List.Perm A A')
  (h : IsIntegralFactorialRatio A B) :
-- imply
  IsIntegralFactorialRatio A' B := by
-- proof
  obtain ⟨hA, hB, hsum, hdvd⟩ := h
  refine ⟨?_, hB, ?_, ?_⟩
  · intro a ha
    exact hA a ((hperm.symm.mem_iff).mp ha)
  · rw [← hperm.sum_eq]
    exact hsum
  · intro n
    rw [← factorialProd_perm hperm]
    exact hdvd n

/--
[isIntegralFactorialRatio_perm_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma isIntegralFactorialRatio_perm_right
  {A B B' : List ℕ}
-- given
  (hperm : List.Perm B B')
  (h : IsIntegralFactorialRatio A B) :
-- imply
  IsIntegralFactorialRatio A B' := by
-- proof
  obtain ⟨hA, hB, hsum, hdvd⟩ := h
  refine ⟨hA, ?_, ?_, ?_⟩
  · intro b hb
    exact hB b ((hperm.symm.mem_iff).mp hb)
  · rw [← hperm.sum_eq]
    exact hsum
  · intro n
    rw [← factorialProd_perm hperm]
    exact hdvd n

/--
[isIntegralFactorialRatio_perm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma isIntegralFactorialRatio_perm
  {A A' B B' : List ℕ}
-- given
  (hA : List.Perm A A')
  (hB : List.Perm B B')
  (h : IsIntegralFactorialRatio A B) :
-- imply
  IsIntegralFactorialRatio A' B' :=
-- proof
  isIntegralFactorialRatio_perm_right hB (isIntegralFactorialRatio_perm_left hA h)

/--
[isIntegralFactorialRatio_refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma isIntegralFactorialRatio_refl
  {L : List ℕ}
-- given
  (hpos : ∀ a ∈ L, 0 < a) :
-- imply
  IsIntegralFactorialRatio L L :=
-- proof
  ⟨hpos, hpos, rfl, fun _ => dvd_rfl⟩

/--
[isIntegralFactorialRatio_singleton_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma isIntegralFactorialRatio_singleton_self
  {c : ℕ}
-- given
  (hc : 0 < c) :
-- imply
  IsIntegralFactorialRatio [c] [c] := by
-- proof
  refine ⟨?_, ?_, rfl, fun _ => dvd_rfl⟩
  · intro a ha
    rwa [List.mem_singleton.mp ha]
  · intro b hb
    rwa [List.mem_singleton.mp hb]

/--
[isIntegralFactorialRatio_centralBinom](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
lemma isIntegralFactorialRatio_centralBinom
  :
-- imply
  IsIntegralFactorialRatio [2] [1, 1] := by
-- proof
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro a ha
    rw [List.mem_singleton.mp ha]
    decide
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hb
    rw [hb]
    decide
  · intro n
    have h := Nat.factorial_mul_factorial_dvd_factorial_add n n
    have h2 : n + n = 2 * n := by omega
    rw [h2] at h
    simpa [factorialProd] using h


-- created on 2026-10-20
-- updated on 2026-10-23
