import Mathlib
import sympy.Basic


/--
[AlgHom_exists_eq_comp_evalAlgHom_of_isDomain](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_exists_eq_comp_evalAlgHom_of_isDomain.lean)
-/

def factorComponent
  {K : Type*}
  [Field K]
  {Ω : Type*}
  [CommRing Ω]
  [Algebra K Ω]
  {J : Type*}
  {A : J → Type*}
  [∀ j, CommRing (A j)]
  [∀ j, Algebra K (A j)]
  [DecidableEq J] (φ : (Π j, A j) →ₐ[K] Ω) (j : J)
  (h1 : φ (Pi.single j 1) = 1) : (A j) →ₐ[K] Ω where
  toFun x :=
    φ (Pi.single j x)
  map_one' :=
    h1
  map_mul' x y := by
    rw [Pi.single_mul, map_mul]
  map_zero' := by
    rw [Pi.single_zero, map_zero]
  map_add' x y := by
    rw [Pi.single_add, map_add]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Pi.single_smul, map_smul, h1]
    exact (Algebra.algebraMap_eq_smul_one r).symm

private lemma single_mul_single_one
  {K : Type*}
  [Field K]
  {Ω : Type*}
  [CommRing Ω]
  [Algebra K Ω]
  {J : Type*}
  {A : J → Type*}
  [∀ j, CommRing (A j)]
  [∀ j, Algebra K (A j)]
  [DecidableEq J] {j j' : J} (h : j ≠ j') (a : A j) :
  (Pi.single j a : Π j, A j) * Pi.single j' 1 = 0 := by
  funext k
  simp only [Pi.mul_apply, Pi.zero_apply]
  obtain rfl | hk := eq_or_ne k j'
  · rw [Pi.single_eq_of_ne (Ne.symm h), zero_mul]
  · rw [Pi.single_eq_of_ne hk, mul_zero]

private lemma exists_factor_algHom
  {K : Type*}
  [Field K]
  {Ω : Type*}
  [CommRing Ω]
  [Algebra K Ω]
  {J : Type*}
  {A : J → Type*}
  [∀ j, CommRing (A j)]
  [∀ j, Algebra K (A j)]
  [Finite J] [IsDomain Ω] (φ : (Π j, A j) →ₐ[K] Ω) :
  ∃ (j : J) (φ₀ : (A j) →ₐ[K] Ω), φ = φ₀.comp (Pi.evalAlgHom K A j) := by
  cases nonempty_fintype J
  classical
  have hidem : ∀ j, φ (Pi.single j 1) = 0 ∨ φ (Pi.single j 1) = 1 := by
    intro j
    have h2 : φ (Pi.single j 1) * φ (Pi.single j 1) = φ (Pi.single j 1) := by
      rw [← map_mul, ← Pi.single_mul, one_mul]
    have h3 : φ (Pi.single j 1) * (φ (Pi.single j 1) - 1) = 0 := by
      rw [mul_sub, h2, mul_one, sub_self]
    obtain h | h := mul_eq_zero.mp h3
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hsum : (∑ j, φ (Pi.single j 1)) = 1 := by
    rw [← map_sum]
    have h1 : (∑ j, (Pi.single j 1 : Π j, A j)) = 1 := by
      simpa using Finset.univ_sum_single (1 : Π j, A j)
    rw [h1, map_one]
  have hex : ∃ j, φ (Pi.single j 1) = 1 := by
    by_contra hno
    have hall : ∀ j ∈ Finset.univ, φ (Pi.single (M := A) j 1) = 0 :=
      fun j _ => (hidem j).resolve_right fun h1 => hno ⟨j, h1⟩
    rw [Finset.sum_eq_zero hall] at hsum
    exact zero_ne_one hsum
  obtain ⟨j₀, h1⟩ := hex
  refine ⟨j₀, factorComponent φ j₀ h1, AlgHom.ext fun g => ?_⟩
  have hg : φ g = ∑ j, φ (Pi.single j (g j)) := by
    rw [← map_sum, Finset.univ_sum_single]
  have hzero : ∀ j ∈ Finset.univ, j ≠ j₀ → φ (Pi.single j (g j)) = 0 := by
    intro j _ hj
    have horth : φ (Pi.single j (g j)) * φ (Pi.single j₀ 1) = 0 := by
      rw [← map_mul, single_mul_single_one (K := K) (Ω := Ω) (J := J) (A := A) hj (g j), map_zero]
    rwa [h1, mul_one] at horth
  calc
    _ = ∑ j, φ (Pi.single j (g j)) := hg
    _ = φ (Pi.single j₀ (g j₀)) :=
      Finset.sum_eq_single j₀ hzero (fun h => absurd (Finset.mem_univ j₀) h)
    _ = (factorComponent φ j₀ h1).comp (Pi.evalAlgHom K A j₀) g := by
      simp [factorComponent, AlgHom.comp_apply, Pi.evalAlgHom_apply]


@[path]
private lemma main
  [Field K] [CommRing Ω] [Algebra K Ω] [IsDomain Ω] [_root_.Finite J]
  {A : J → Type*} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]
  {φ : (Π j, A j) →ₐ[K] Ω} :
-- imply
  ∃ (j : J) (φ₀ : (A j) →ₐ[K] Ω), φ = φ₀.comp (Pi.evalAlgHom K A j) :=
-- proof
  exists_factor_algHom φ


-- created on 2026-10-10
