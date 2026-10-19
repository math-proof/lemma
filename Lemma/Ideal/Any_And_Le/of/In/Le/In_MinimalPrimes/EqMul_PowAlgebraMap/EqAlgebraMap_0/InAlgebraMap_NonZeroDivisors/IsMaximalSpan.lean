import Mathlib
import sympy.Basic
set_option maxHeartbeats 1000000
open scoped TensorProduct nonZeroDivisors


private lemma exists_minimalPrimes_le_not_mem
  [CommRing T] [IsReduced T]
  {𝔮 : Ideal T} [𝔮.IsPrime]
  {c : T}
-- given
  (hAnn : ∀ u, u * c = 0 → u ∈ 𝔮) :
-- imply
  ∃ P ∈ minimalPrimes T, P ≤ 𝔮 ∧ c ∉ P := by
-- proof
  let S : Submonoid T := 𝔮.primeCompl ⊔ Submonoid.powers c
  have hS : Disjoint ((⊥ : Ideal T) : Set T) (S : Set T) := by
    rw [Set.disjoint_left]
    intro x hx hxS
    have hx0 : x = 0 := hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submonoid.mem_sup.mp hxS
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hz
    apply hy
    match m with
    | 0 =>
      rw [pow_zero, mul_one] at hx0
      rw [hx0]
      apply 𝔮.zero_mem
    | m + 1 =>
      apply hAnn
      apply IsReduced.eq_zero
      refine ⟨m + 1, ?_⟩
      rw [mul_pow, pow_succ y, mul_assoc, hx0]
      simp
  obtain ⟨P, hP, -, hPS⟩ := Ideal.exists_le_prime_disjoint ⊥ S hS
  have hP𝔮 : P ≤ 𝔮 := fun x hx => by
    by_contra hx'
    apply Set.disjoint_left.mp hPS hx (Submonoid.mem_sup_left hx')
  have hcP : c ∉ P := fun hc =>
    Set.disjoint_left.mp hPS hc (Submonoid.mem_sup_right (Submonoid.mem_powers c))
  let _ := hP
  obtain ⟨P₂, hP₂, hP₂P⟩ := Ideal.exists_minimalPrimes_le (show (⊥ : Ideal T) ≤ P from bot_le)
  refine ⟨P₂, hP₂, hP₂P.trans hP𝔮, fun h => hcP (hP₂P h)⟩

private lemma one_tmul_algebraMap_mul
  [CommRing R]
  [CommRing 𝒪] [Algebra R 𝒪]
  [Field κ] [Algebra R κ]
  {π : R}
-- given
  (hπκ : algebraMap R κ π = 0)
  (y : 𝒪) :
-- imply
  (1 : κ) ⊗ₜ[R] (algebraMap R 𝒪 π * y) = 0 := by
-- proof
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, hπκ, TensorProduct.zero_tmul]

private lemma one_tmul_algebraMap
  [CommRing R] [CommRing 𝒪] [Algebra R 𝒪]
  [Field κ] [Algebra R κ]
  (r : R) :
-- imply
  (1 : κ) ⊗ₜ[R] (algebraMap R 𝒪 r) = (algebraMap R κ r) ⊗ₜ[R] (1 : 𝒪) := by
-- proof
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

private lemma φκ_mem
  [CommRing R]
  [Field κ] [Algebra R κ]
  (π : R)
  (hπκ : algebraMap R κ π = 0)
  (a : R)
-- given
  (ha : a ∈ Ideal.span {π}) :
-- imply
  algebraMap R κ a = 0 := by
-- proof
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [map_mul, hπκ, mul_zero]

set_option maxHeartbeats 1000000 in
private noncomputable def φκ
  [CommRing R] (π : R) [Field κ] [Algebra R κ]
  (hπκ : algebraMap R κ π = 0) :
  R ⧸ Ideal.span {π} →+* κ :=
  Ideal.Quotient.lift (Ideal.span {π}) (algebraMap R κ) (fun a ha => φκ_mem π hπκ a ha)

private lemma φB_mem
  [CommRing R] (π : R) [CommRing 𝒪] [Algebra R 𝒪]
  (a : R) (ha : a ∈ Ideal.span {π}) :
-- imply
  ((Ideal.Quotient.mk (Ideal.span {algebraMap R 𝒪 π})).comp (algebraMap R 𝒪)) a = 0 := by
-- proof
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [RingHom.comp_apply, map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

set_option maxHeartbeats 1000000 in
private noncomputable def φB
  [CommRing R] (π : R) [CommRing 𝒪] [Algebra R 𝒪] :
  R ⧸ Ideal.span {π} →+* 𝒪 ⧸ Ideal.span {algebraMap R 𝒪 π} :=
  Ideal.Quotient.lift (Ideal.span {π}) ((Ideal.Quotient.mk _).comp (algebraMap R 𝒪))
    (fun a ha => φB_mem π a ha)

private lemma ρ_mem
  [CommRing R]
  [CommRing 𝒪] [Algebra R 𝒪]
  [Field κ] [Algebra R κ]
  (π : R)
  (hπκ : algebraMap R κ π = 0)
  (a : 𝒪)
-- given
  (ha : a ∈ Ideal.span {algebraMap R 𝒪 π}) :
-- imply
  (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := 𝒪)) a = 0 := by
-- proof
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  show (1 : κ) ⊗ₜ[R] (t * algebraMap R 𝒪 π) = 0
  rw [mul_comm]
  apply one_tmul_algebraMap_mul hπκ t

set_option maxHeartbeats 1000000 in
private noncomputable def ρ
  [CommRing R] (π : R) [CommRing 𝒪] [Algebra R 𝒪]
  [Field κ] [Algebra R κ]
  (hπκ : algebraMap R κ π = 0) :
  𝒪 ⧸ Ideal.span {algebraMap R 𝒪 π} →+* κ ⊗[R] 𝒪 :=
  Ideal.Quotient.lift (Ideal.span {algebraMap R 𝒪 π})
    (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := 𝒪)).toRingHom
    (fun a ha => ρ_mem π hπκ a ha)

private lemma ρ_mk
  [CommRing R]
  [CommRing 𝒪] [Algebra R 𝒪]
  [Field κ] [Algebra R κ]
  {π : R}
  (hπκ : algebraMap R κ π = 0) (s : 𝒪) :
-- imply
  ρ π hπκ (Ideal.Quotient.mk _ s) = (1 : κ) ⊗ₜ[R] s :=
  rfl

private lemma ρ_φB
  [CommRing R]
  [CommRing 𝒪] [Algebra R 𝒪]
  [Field κ] [Algebra R κ]
  {π : R}
  (hπκ : algebraMap R κ π = 0) (c : R ⧸ Ideal.span {π}) :
-- imply
  ρ π hπκ (φB π c) = (φκ π hπκ c) ⊗ₜ[R] (1 : 𝒪) := by
-- proof
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hφB : φB π (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R 𝒪 r) := by
    rw [φB, Ideal.Quotient.lift_mk, RingHom.comp_apply]
  have hφκ : φκ π hπκ (Ideal.Quotient.mk _ r) = algebraMap R κ r := by
    rw [φκ, Ideal.Quotient.lift_mk]
  rw [hφB, ρ_mk, hφκ]
  apply one_tmul_algebraMap r

private lemma exists_tmul_not_mem_and_mul_eq
  [CommRing R]
  [CommRing 𝒪] [Algebra R 𝒪]
  [Field κ] [Algebra R κ]
  {π : R} [(Ideal.span {π}).IsMaximal]
-- given
  (hπκ : algebraMap R κ π = 0)
  {𝔮 : Ideal (κ ⊗[R] 𝒪)} [𝔮.IsPrime]
  {x : κ ⊗[R] 𝒪} (hx : x ∉ 𝔮)
  {c : 𝒪} (hxc : x * ((1 : κ) ⊗ₜ[R] c) = 0) :
-- imply
  ∃ s t : 𝒪, (1 : κ) ⊗ₜ[R] s ∉ 𝔮 ∧ s * c = algebraMap R 𝒪 π * t := by
-- proof
  classical
  let _ : Field (R ⧸ Ideal.span {π}) := Ideal.Quotient.field (Ideal.span {π})
  let _ : Algebra (R ⧸ Ideal.span {π}) κ := (φκ π hπκ).toAlgebra
  let _ : IsScalarTower R (R ⧸ Ideal.span {π}) κ :=
    IsScalarTower.of_algebraMap_eq (fun r => (Ideal.Quotient.lift_mk (Ideal.span {π}) (algebraMap R κ) (φκ_mem π hπκ)).symm)
  let b := Module.Free.chooseBasis (R ⧸ Ideal.span {π}) κ
  have hsmul : ∀ (r : R) (a : κ), b.repr (r • a) = (Ideal.Quotient.mk (Ideal.span {π}) r) • b.repr a := by
    intro r a
    rw [← map_smul, ← IsScalarTower.algebraMap_smul (R ⧸ Ideal.span {π}) r a, Ideal.Quotient.algebraMap_eq]
  let Λ : Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {π}) κ → (κ ⊗[R] 𝒪 →+ 𝒪 ⧸ Ideal.span {algebraMap R 𝒪 π}) :=
    fun j =>
      let fadd : κ → 𝒪 →+ 𝒪 ⧸ Ideal.span {algebraMap R 𝒪 π} := fun a =>
        AddMonoidHom.mk' (fun s => φB π (b.repr a j) * Ideal.Quotient.mk _ s)
          (fun s s' => by simp only [map_add, mul_add])
      have hadd : ∀ a a', fadd (a + a') = fadd a + fadd a' := by
        intro a a'
        ext s
        simp only [fadd, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, Finsupp.add_apply, add_mul]
      let fκ := AddMonoidHom.mk' fadd hadd
      have hcompat : ∀ (r : R) (a : κ) (s : 𝒪), fκ (r • a) s = fκ a (r • s) := by
        intro r a s
        show φB π (b.repr (r • a) j) * Ideal.Quotient.mk _ s = φB π (b.repr a j) * Ideal.Quotient.mk _ (r • s)
        rw [hsmul, Finsupp.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def, map_mul]
        have : φB π (Ideal.Quotient.mk (Ideal.span {π}) r) = Ideal.Quotient.mk _ (algebraMap R 𝒪 r) := by
          rw [φB, Ideal.Quotient.lift_mk, RingHom.comp_apply]
        rw [this]
        ring
      TensorProduct.liftAddHom fκ hcompat
  have hΛ : ∀ j (a : κ) (s : 𝒪), Λ j (a ⊗ₜ[R] s) = φB π (b.repr a j) * Ideal.Quotient.mk _ s :=
    fun j a s => TensorProduct.liftAddHom_tmul _ _ _ _
  have hΛmul : ∀ j (y : κ ⊗[R] 𝒪), Λ j (y * ((1 : κ) ⊗ₜ[R] c)) = Λ j y * Ideal.Quotient.mk _ c := by
    intro j y
    refine TensorProduct.inductionOn
      (motive := fun y => Λ j (y * ((1 : κ) ⊗ₜ[R] c)) = Λ j y * Ideal.Quotient.mk _ c) y ?_ ?_
    ·
      intro a s
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hΛ, hΛ, map_mul, mul_assoc]
    ·
      intro y z hy hz
      rw [add_mul, map_add, map_add, hy, hz, add_mul]
  have hterm : ∀ j (a : κ) (s : 𝒪),
      (b j ⊗ₜ[R] (1 : 𝒪)) * ρ π hπκ (Λ j (a ⊗ₜ[R] s)) = ((b.repr a j) • b j) ⊗ₜ[R] s := by
    intro j a s
    rw [hΛ, map_mul, ρ_φB, ρ_mk, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [mul_one, one_mul]
    rw [Algebra.smul_def, mul_comm (b j)]
    rfl
  have hrec : ∀ y : κ ⊗[R] 𝒪, ∃ F : Finset (Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {π}) κ),
      ∀ G, F ⊆ G → (∑ j ∈ G, (b j ⊗ₜ[R] (1 : 𝒪)) * ρ π hπκ (Λ j y)) = y := by
    intro y
    refine TensorProduct.inductionOn
      (motive := fun y => ∃ F : Finset (Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {π}) κ),
        ∀ G, F ⊆ G → (∑ j ∈ G, (b j ⊗ₜ[R] (1 : 𝒪)) * ρ π hπκ (Λ j y)) = y) y ?_ ?_
    ·
      intro a s
      refine ⟨(b.repr a).support, fun G hG => ?_⟩
      simp_rw [hterm]
      rw [← TensorProduct.sum_tmul]
      congr 1
      rw [← Finset.sum_subset hG (fun j _ hj => by rw [Finsupp.notMem_support_iff.mp hj, zero_smul])]
      conv_rhs => rw [← b.linearCombination_repr a]
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
    ·
      intro y z hy hz
      obtain ⟨Fy, hFy⟩ := hy
      obtain ⟨Fz, hFz⟩ := hz
      refine ⟨Fy ∪ Fz, fun G hG => ?_⟩
      simp_rw [map_add, mul_add]
      rw [Finset.sum_add_distrib, hFy G (Finset.union_subset_left hG), hFz G (Finset.union_subset_right hG)]
  obtain ⟨F, hF⟩ := hrec x
  have hj : ∃ j, ρ π hπκ (Λ j x) ∉ 𝔮 := by
    by_contra h
    push Not at h
    apply hx
    rw [← hF F (Finset.Subset.refl F)]
    apply Ideal.sum_mem _ (fun j _ => Ideal.mul_mem_left _ _ (h j))
  obtain ⟨j, hj⟩ := hj
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (Λ j x)
  refine ⟨s, ?_⟩
  have hsc : Ideal.Quotient.mk (Ideal.span {algebraMap R 𝒪 π}) (s * c) = 0 := by
    rw [map_mul, hs, ← hΛmul, hxc, map_zero]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hsc)
  refine ⟨t, ?_, ?_⟩
  ·
    rw [← ρ_mk (π := π) hπκ, hs]
    apply hj
  · rw [← ht, mul_comm]


/--
[Algebra_TensorProduct_exists_mem_minimalPrimes_ne_and_le_of_mul_eq_pow_of_tmul_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_exists_mem_minimalPrimes_ne_and_le_of_mul_eq_pow_of_tmul_mem.lean)
-/
@[path]
private lemma main
  [CommRing R]
  [CommRing 𝒪] [Algebra R 𝒪]
  [Field κ] [Algebra R κ]
  [IsReduced (κ ⊗[R] 𝒪)]
  {Q₀ 𝔮 : Ideal (κ ⊗[R] 𝒪)} [𝔮.IsPrime]
  {π : R} {v v' : 𝒪} {n : ℕ}
-- given
  (hπ : (Ideal.span {π}).IsMaximal)
  (hπ𝒪 : algebraMap R 𝒪 π ∈ nonZeroDivisors 𝒪)
  (hπκ : algebraMap R κ π = 0)
  (hvv' : v * v' = algebraMap R 𝒪 π ^ n)
  (hQ₀ : Q₀ ∈ minimalPrimes (κ ⊗[R] 𝒪))
  (_ : Q₀ ≤ 𝔮)
  (hv₀ : (1 : κ) ⊗ₜ[R] v ∉ Q₀)
  (hv : (1 : κ) ⊗ₜ[R] v ∈ 𝔮) :
-- imply
  ∃ Q₁ ∈ minimalPrimes (κ ⊗[R] 𝒪), Q₁ ≠ Q₀ ∧ Q₁ ≤ 𝔮 := by
-- proof
  let _ : (Ideal.span {π}).IsMaximal := hπ
  let hQ₀p : Q₀.IsPrime := hQ₀.1.1
  by_contra hne
  push Not at hne
  have hkill : ∀ c ∈ Q₀, ∃ u ∉ 𝔮, u * c = 0 := by
    intro c hc
    by_contra h
    push Not at h
    obtain ⟨P, hP, hP𝔮, hcP⟩ := exists_minimalPrimes_le_not_mem (𝔮 := 𝔮) (c := c) (fun u hu => by
      by_contra hu'
      apply h u hu' hu)
    apply hne P hP (fun hPQ => hcP (hPQ ▸ hc)) hP𝔮
  have key : ∀ (m : ℕ) (S t : 𝒪), (1 : κ) ⊗ₜ[R] S ∉ 𝔮 → S * algebraMap R 𝒪 π ^ m = t * v → False := by
    intro m
    induction m with
    | zero =>
      intro S t hS hSt
      apply hS
      rw [pow_zero, mul_one] at hSt
      have h1 : (1 : κ) ⊗ₜ[R] (t * v) = ((1 : κ) ⊗ₜ[R] t) * ((1 : κ) ⊗ₜ[R] v) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hSt, h1]
      apply Ideal.mul_mem_left _ _ hv
    | succ m ih =>
      intro S t hS hSt
      have ht : (1 : κ) ⊗ₜ[R] t ∈ Q₀ := by
        apply (hQ₀p.mem_or_mem (by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hSt, pow_succ, mul_comm _ (algebraMap R 𝒪 π), ← mul_assoc, mul_comm S, mul_assoc, one_tmul_algebraMap_mul hπκ]; apply Q₀.zero_mem)).resolve_right hv₀
      obtain ⟨u, hu, hut⟩ := hkill _ ht
      obtain ⟨s, t', hs, hst⟩ := exists_tmul_not_mem_and_mul_eq (π := π) hπκ (x := u) hu (c := t) hut
      refine ih (S * s) t' ?_ ?_
      ·
        rw [← one_mul (1 : κ), ← Algebra.TensorProduct.tmul_mul_tmul]
        intro h
        apply ((inferInstance : 𝔮.IsPrime).mem_or_mem h).elim hS hs
      ·
        have h1 : (S * s * algebraMap R 𝒪 π ^ m - t' * v) * algebraMap R 𝒪 π = 0 := by
          have := congrArg (fun z => s * z) hSt
          rw [sub_mul, sub_eq_zero]
          calc
            _ = s * (S * algebraMap R 𝒪 π ^ (m + 1)) := by ring
            _ = s * (t * v) := this
            _ = (s * t) * v := by ring
            _ = algebraMap R 𝒪 π * t' * v := by rw [hst]
            _ = t' * v * algebraMap R 𝒪 π := by ring
        have h2 := (mem_nonZeroDivisors_iff.mp hπ𝒪).2 _ h1
        rwa [sub_eq_zero] at h2
  refine key n 1 v' ?_ ?_
  ·
    rw [← Algebra.TensorProduct.one_def]
    intro h
    apply (inferInstance : 𝔮.IsPrime).ne_top
    apply (Ideal.eq_top_iff_one 𝔮).mpr h
  · rw [one_mul, mul_comm, hvv']


-- created on 2026-10-13
