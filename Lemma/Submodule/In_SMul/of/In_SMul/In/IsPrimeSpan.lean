import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped Pointwise


/-- ported from external source -/
@[path]
private lemma main
  [CommRing A] [AddCommGroup M] [Module A M] [Module.Projective A M] [AddCommGroup N] [Module A N]
  {ϖ : A}
  {𝔭 : Ideal A} [𝔭.IsPrime]
  {f : M →ₗ[A] N} [IsLocalizedModule 𝔭.primeCompl f]
  {m : M}
-- given
  (hϖ : (Ideal.span {ϖ} : Ideal A).IsPrime)
  (h𝔭 : ϖ ∈ 𝔭)
  (hm : f m ∈ ϖ • (⊤ : Submodule A N)) :
-- imply
  m ∈ ϖ • (⊤ : Submodule A M) := by
  classical
    set S := 𝔭.primeCompl with hSdef
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm
    obtain ⟨⟨m', s⟩, hms⟩ := IsLocalizedModule.mk'_surjective S f y
    simp only [Function.uncurry_apply_pair] at hms
    have h1 : f ((s : A) • m) = f (ϖ • m') := by
-- proof
      calc f ((s : A) • m) = (s : A) • f m := f.map_smul _ _
        _ = ϖ • ((s : A) • y) := by rw [← hy, smul_comm]
        _ = ϖ • (s • IsLocalizedModule.mk' f m' s) := by rw [hms]; rfl
        _ = ϖ • f m' := by rw [IsLocalizedModule.mk'_cancel']
        _ = f (ϖ • m') := (f.map_smul _ _).symm
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists S f).mp h1
    have hc' : (c : A) • (s : A) • m = (c : A) • ϖ • m' := hc
    set u : A := (c : A) * (s : A) with hu
    have huS : u ∈ S := S.mul_mem c.2 s.2
    have hum : u • m = ϖ • ((c : A) • m') := by
      rw [hu, mul_smul, hc', smul_comm]
    have huϖ : u ∉ (Ideal.span {ϖ} : Ideal A) := fun h =>
      huS ((Ideal.span_singleton_le_iff_mem 𝔭).mpr h𝔭 h)
    obtain ⟨sec, hsec⟩ := Module.Projective.out (R := A) (P := M)
    set v : M →₀ A := sec m with hv
    have hcoord : ∀ i, v i ∈ (Ideal.span {ϖ} : Ideal A) := by
      intro i
      have h2 : u * v i = ϖ * sec ((c : A) • m') i := by
        have := congrArg (fun w : M →₀ A => w i) (congrArg sec hum)
        simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using this
      have h3 : u * v i ∈ (Ideal.span {ϖ} : Ideal A) :=
        h2 ▸ Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)
      refine (hϖ.mem_or_mem h3).resolve_left huϖ
    have hdiv : ∀ i, ∃ b : A, ϖ * b = v i := fun i => by
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (hcoord i)
      exact ⟨b, by rw [mul_comm, hb]⟩
    choose b hb using hdiv
    set g : M →₀ A := Finsupp.onFinset v.support (fun i => if v i = 0 then 0 else b i) (by
      intro i hi
      rw [Finsupp.mem_support_iff]
      intro h0
      exact hi (ite_eq_left h0)) with hg
    have hϖg : ϖ • g = v := by
      ext i
      rw [Finsupp.smul_apply, hg, Finsupp.onFinset_apply, smul_eq_mul]
      by_cases h0 : v i = 0
      · rw [ite_eq_left h0, mul_zero, h0]
      · rw [ite_eq_right h0, hb]
    have hm' : m = ϖ • Finsupp.linearCombination A id g := by
      rw [← map_smul, hϖg, hv]
      exact (hsec m).symm
    rw [hm']
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top


-- created on 2026-10-23
