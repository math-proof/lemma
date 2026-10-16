import Mathlib
import sympy.Basic
open IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin Pointwise


private lemma isNoetherianRing_adjoin
  [Field k] [Field F] [Algebra k F]
  (y : F) :
-- imply
  IsNoetherianRing (Algebra.adjoin k ({y} : Set F)) :=
  isNoetherianRing_of_fg ⟨{y}, by rw [Finset.coe_singleton]⟩

private lemma fg_of_image_le
  [Field k] [Field F] [Algebra k F]
  {A A' : Subalgebra k F}
  (φ : F →+* F)
-- given
  (hφ : Function.Injective φ)
  (hlift : ∀ a' ∈ A', ∃ a ∈ A, φ a = a')
  [IsNoetherianRing A']
  {M' : Submodule A' F} (hM' : M'.FG)
  {B : Submodule A F} (hB : ∀ b ∈ B, φ b ∈ M') :
-- imply
  B.FG := by
-- proof
  classical
  let _ : IsNoetherian A' M' := isNoetherian_of_fg_of_noetherian M' hM'
  let P : Submodule A' F :=
    { carrier := φ '' (B : Set F)
      add_mem' := by
        intro _ _ hb hc
        obtain ⟨b, hb, rfl⟩ := hb
        obtain ⟨c, hc, rfl⟩ := hc
        refine ⟨b + c, add_mem hb hc, map_add φ b c⟩
      zero_mem' := by
        refine ⟨0, zero_mem _, map_zero φ⟩
      smul_mem' := by
        intro a' _ hb
        obtain ⟨b, hb, rfl⟩ := hb
        obtain ⟨a, ha, hφa⟩ := hlift a' a'.2
        refine ⟨(⟨a, ha⟩ : A) • b, B.smul_mem _ hb, ?_⟩
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        change φ a * φ b = (a' : F) * φ b
        rw [hφa] }
  have hPM' : P ≤ M' := by
    intro _ h
    obtain ⟨b, hb, rfl⟩ := h
    apply hB b hb
  have hPfg : P.FG := (isNoetherian_submodule.mp inferInstance) P hPM'
  obtain ⟨G, hG⟩ := hPfg
  have hGP : ∀ g ∈ G, ∃ b ∈ B, φ b = g := by
    intro g hg
    have : g ∈ P := hG ▸ Submodule.subset_span hg
    apply this
  choose t ht htφ using hGP
  let T : Finset F := G.attach.image fun g => t g.1 g.2
  have hTB : (T : Set F) ⊆ B := by
    intro y hy
    rw [Finset.coe_image] at hy
    obtain ⟨g, _, rfl⟩ := hy
    apply ht g.1 g.2
  have hkey : ∀ y ∈ P, ∃ c ∈ Submodule.span A (T : Set F), φ c = y := by
    intro y hy
    rw [← hG] at hy
    induction hy using Submodule.span_induction with
    | mem g hg =>
      refine ⟨t g hg, Submodule.subset_span ?_, htφ g hg⟩
      rw [Finset.mem_coe]
      apply Finset.mem_image.mpr ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩
    | zero =>
      refine ⟨0, zero_mem _, map_zero φ⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨d, hd, rfl⟩ := hz
      refine ⟨c + d, add_mem hc hd, map_add φ c d⟩
    | smul a' y _ hy =>
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨a, ha, hφa⟩ := hlift a' a'.2
      refine ⟨(⟨a, ha⟩ : A) • c, Submodule.smul_mem _ _ hc, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      change φ a * φ c = (a' : F) * φ c
      rw [hφa]
  refine ⟨T, le_antisymm (Submodule.span_le.mpr hTB) ?_⟩
  intro b hb
  obtain ⟨c, hc, hφc⟩ := hkey (φ b) ⟨b, hb, rfl⟩
  rw [← hφ hφc]
  apply hc

private lemma fg_toSubmodule_integralClosure_of_isSeparable
  [Field k] [Field F] [Algebra k F]
  {x : F}
-- given
  (hx : Transcendental k x)
  (E : IntermediateField (IntermediateField.adjoin k ({x} : Set F)) F)
  [FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) E]
  [Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) E] :
-- imply
  (Subalgebra.toSubmodule (integralClosure (Algebra.adjoin k ({x} : Set F)) E)).FG := by
-- proof
  let 𝓐 := Algebra.adjoin k ({x} : Set F)
  let 𝓚 := IntermediateField.adjoin k ({x} : Set F)
  let _ : UniqueFactorizationMonoid 𝓐 := hx.uniqueFactorizationMonoid_adjoin
  let _ : IsIntegrallyClosed 𝓐 := inferInstance
  let _ : IsNoetherianRing 𝓐 := isNoetherianRing_adjoin x
  let _ : Algebra 𝓐 (integralClosure 𝓐 E) := Subalgebra.algebra (integralClosure 𝓐 E)
  let _ : SMul 𝓐 (integralClosure 𝓐 E) := Algebra.toSMul
  let _ : IsScalarTower 𝓐 (integralClosure 𝓐 E) E :=
    IsScalarTower.subalgebra' 𝓐 E E (integralClosure 𝓐 E)
  apply Module.Finite.iff_fg.mp (IsIntegralClosure.finite 𝓐 𝓚 E (integralClosure 𝓐 E))

private lemma exists_fg_of_isSeparable
  [Field k] [Field F] [Algebra k F]
  {x : F}
-- given
  (hx : Transcendental k x)
  (E : IntermediateField (IntermediateField.adjoin k ({x} : Set F)) F)
  [FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) E]
  [Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) E] :
-- imply
  ∃ N : Submodule (Algebra.adjoin k ({x} : Set F)) F,
    N.FG ∧ ∀ f : F, f ∈ E → IsIntegral (Algebra.adjoin k ({x} : Set F)) f → f ∈ N := by
-- proof
  let 𝓐 := Algebra.adjoin k ({x} : Set F)
  have h1 := fg_toSubmodule_integralClosure_of_isSeparable hx E
  let ψ : E →ₗ[𝓐] F := ((IntermediateField.val E).restrictScalars 𝓐).toLinearMap
  refine ⟨(Subalgebra.toSubmodule (integralClosure 𝓐 E)).map ψ, h1.map _, ?_⟩
  intro f hf hint
  refine ⟨⟨f, hf⟩, ?_, rfl⟩
  change IsIntegral 𝓐 (⟨f, hf⟩ : E)
  have : ((IntermediateField.val E).restrictScalars 𝓐) ⟨f, hf⟩ = f := rfl
  rw [← this] at hint
  apply (isIntegral_algHom_iff _ Subtype.val_injective).mp hint

private lemma exists_pow_mem_separableClosure
  [Field k] [Field F] [Algebra k F]
  {x : F} [FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F] :
-- imply
  ∃ p e : ℕ, ExpChar F p ∧ ∀ f : F,
    f ^ p ^ e ∈ separableClosure (IntermediateField.adjoin k ({x} : Set F)) F := by
-- proof
  let 𝓚 := IntermediateField.adjoin k ({x} : Set F)
  let _ : IsPurelyInseparable (separableClosure 𝓚 F) F :=
    separableClosure.isPurelyInseparable 𝓚 F
  refine ⟨ringExpChar F, IsPurelyInseparable.exponent (separableClosure 𝓚 F) F, inferInstance, fun f => ?_⟩
  obtain ⟨y, hy⟩ :=
    IsPurelyInseparable.exponent_def' (separableClosure 𝓚 F) (L := F) (ringExpChar F) f
  rw [← hy]
  apply y.2

private lemma exists_pow_eq_of_mem_adjoin_pow
  [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
  {x : F} {p e : ℕ} [ExpChar F p]
  {a' : F}
-- given
  (ha' : a' ∈ Algebra.adjoin k ({x ^ p ^ e} : Set F)) :
-- imply
  ∃ a ∈ Algebra.adjoin k ({x} : Set F), a ^ p ^ e = a' := by
-- proof
  induction ha' using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    refine ⟨x, Algebra.self_mem_adjoin_singleton k x, hy.symm⟩
  | algebraMap c =>
    obtain ⟨d, rfl⟩ := IsAlgClosed.exists_pow_nat_eq c (pow_pos (expChar_pos F p) e)
    refine ⟨algebraMap k F d, Subalgebra.algebraMap_mem _ d, ?_⟩
    rw [map_pow]
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, hb, rfl⟩ := hz
    refine ⟨a + b, add_mem ha hb, add_pow_expChar_pow a b p e⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, hb, rfl⟩ := hz
    refine ⟨a * b, mul_mem ha hb, mul_pow a b _⟩

private lemma exists_fg_adjoin_pow_of_fg
  [Field k] [Field F] [Algebra k F]
  {x : F} {q : ℕ}
-- given
  (hq : 0 < q)
  {N : Submodule (Algebra.adjoin k ({x} : Set F)) F} (hN : N.FG) :
-- imply
  ∃ M' : Submodule (Algebra.adjoin k ({x ^ q} : Set F)) F, M'.FG ∧ ∀ f ∈ N, f ∈ M' := by
-- proof
  let 𝓐 := Algebra.adjoin k ({x} : Set F)
  let Aq := Algebra.adjoin k ({x ^ q} : Set F)
  have hxq : x ^ q ∈ Aq := Algebra.self_mem_adjoin_singleton k _
  have hxint : IsIntegral Aq x :=
    IsIntegral.of_pow hq (isIntegral_algebraMap (A := F) (x := (⟨x ^ q, hxq⟩ : Aq)))
  obtain ⟨t, ht⟩ := hxint.fg_adjoin_singleton
  have hAA₁ : ∀ a ∈ 𝓐, a ∈ Algebra.adjoin Aq ({x} : Set F) := by
    intro a ha
    have h1 : Algebra.adjoin k ({x} : Set F) ≤ Algebra.adjoin k ({x ^ q} ∪ {x} : Set F) :=
      Algebra.adjoin_mono Set.subset_union_right
    have h2 := Algebra.adjoin_union_eq_adjoin_adjoin k ({x ^ q} : Set F) ({x} : Set F)
    have := h1 ha
    rw [h2] at this
    apply this
  obtain ⟨S, hS⟩ := hN
  refine ⟨Submodule.span _ ((t : Set F) • (S : Set F)),
    Submodule.fg_span (Set.Finite.smul t.finite_toSet S.finite_toSet), ?_⟩
  have hstable : ∀ a ∈ Algebra.adjoin Aq ({x} : Set F),
      ∀ m ∈ Submodule.span Aq ((t : Set F) • (S : Set F)), a * m ∈ Submodule.span Aq ((t : Set F) • (S : Set F)) := by
    intro a ha m hm
    induction hm using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨ti, hti, sj, hsj, rfl⟩ := Set.mem_smul.mp hy
      have hti' : ti ∈ Algebra.adjoin Aq ({x} : Set F) := by
        rw [← Subalgebra.mem_toSubmodule, ← ht]
        apply Submodule.subset_span hti
      have hat : a * ti ∈ Submodule.span Aq (t : Set F) := by
        rw [ht, Subalgebra.mem_toSubmodule]
        apply mul_mem ha hti'
      have hassoc : a * ti • sj = (a * ti) • sj := by
        simp only [smul_eq_mul, mul_assoc]
      rw [hassoc]
      apply Submodule.smul_mem_span_smul_of_mem hat hsj
    | zero =>
      rw [mul_zero]
      apply zero_mem
    | add y z _ _ hy hz =>
      rw [mul_add]
      apply add_mem hy hz
    | smul a' y _ hy =>
      rw [mul_smul_comm]
      apply Submodule.smul_mem _ _ hy
  intro f hf
  rw [← hS] at hf
  induction hf using Submodule.span_induction with
  | mem s hs =>
    have h1 : (1 : F) ∈ Submodule.span Aq (t : Set F) := by
      rw [ht, Subalgebra.mem_toSubmodule]
      apply one_mem
    have := Submodule.smul_mem_span_smul_of_mem h1 hs
    rwa [one_smul] at this
  | zero =>
    apply zero_mem
  | add y z _ _ hy hz =>
    apply add_mem hy hz
  | smul a y _ hy =>
    rw [Algebra.smul_def]
    apply hstable _ (hAA₁ _ a.2) _ hy

private lemma fg_toSubmodule_integralClosure
  [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
  {x : F}
-- given
  (hx : Transcendental k x)
  (hfd : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
-- imply
  (Subalgebra.toSubmodule (integralClosure (Algebra.adjoin k ({x} : Set F)) F)).FG := by
-- proof
  let 𝓐 := Algebra.adjoin k ({x} : Set F)
  let 𝓚 := IntermediateField.adjoin k ({x} : Set F)
  obtain ⟨N, hNfg, hN⟩ := exists_fg_of_isSeparable hx (separableClosure 𝓚 F)
  obtain ⟨p, e, hp, hpe⟩ := exists_pow_mem_separableClosure (k := k) (x := x)
  let _ := hp
  have hq0 : 0 < p ^ e := pow_pos (expChar_pos F p) e
  let φ : F →+* F := iterateFrobenius F p e
  have hφ : ∀ f : F, φ f = f ^ p ^ e := fun f => iterateFrobenius_def p e f
  obtain ⟨M', hM'fg, hNM'⟩ := exists_fg_adjoin_pow_of_fg (x := x) hq0 hNfg
  let _ : IsNoetherianRing (Algebra.adjoin k ({x ^ p ^ e} : Set F)) :=
    isNoetherianRing_adjoin (x ^ p ^ e)
  refine fg_of_image_le φ φ.injective ?_ hM'fg ?_
  ·
    intro a' ha'
    obtain ⟨a, ha, h⟩ := exists_pow_eq_of_mem_adjoin_pow (x := x) (p := p) (e := e) ha'
    refine ⟨a, ha, ?_⟩
    rw [hφ, h]
  ·
    intro b hb
    refine hNM' _ (hN _ ?_ ?_)
    ·
      rw [hφ]
      apply hpe b
    ·
      rw [hφ]
      apply IsIntegral.pow hb


/--
[Algebra_finite_integralClosure_adjoin_singleton_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_finite_integralClosure_adjoin_singleton_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
  {x : F}
-- given
  (hx : Transcendental k x)
  (hfd : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
-- imply
  Module.Finite (Algebra.adjoin k ({x} : Set F))
    (integralClosure (Algebra.adjoin k ({x} : Set F)) F) :=
  Module.Finite.iff_fg.mpr (fg_toSubmodule_integralClosure (x := x) hx hfd)


-- created on 2026-10-13
