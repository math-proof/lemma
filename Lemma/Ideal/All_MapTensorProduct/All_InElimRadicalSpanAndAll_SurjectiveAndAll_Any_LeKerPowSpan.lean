import Mathlib
import sympy.Basic
open scoped TensorProduct
open Function


section One

variable (𝓞 : Type u) [CommRing 𝓞] (p : ℕ) [Algebra 𝓞 (ZMod p)] (R : ℕ → Type v) [∀ v, CommRing (R v)] [∀ v, Algebra 𝓞 (R v)] (t : ∀ v, R (v + 1) →ₐ[𝓞] R v) {σ : Type w} (x : ∀ v, σ → R v)

private noncomputable abbrev φ (v : ℕ) : MvPolynomial σ (ZMod p) →ₐ[ZMod p] ZMod p ⊗[𝓞] R v :=
  MvPolynomial.aeval fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i

variable {p R t x}

private lemma map_comp_φ (hxt : ∀ v i, t v (x (v + 1) i) = x v i) (v : ℕ) :
  (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (t v)).comp (φ 𝓞 p R x (v + 1)) = φ 𝓞 p R x v := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, hxt v i]

private lemma ker_φ_anti (hxt : ∀ v i, t v (x (v + 1) i) = x v i) {v w : ℕ} (h : v ≤ w) :
  RingHom.ker (φ 𝓞 p R x w) ≤ RingHom.ker (φ 𝓞 p R x v) := by
  induction h with
  | refl => exact le_rfl
  | @step w _ ih =>
    refine le_trans ?_ ih
    intro P hP
    rw [RingHom.mem_ker] at hP ⊢
    rw [← map_comp_φ 𝓞 hxt w, AlgHom.comp_apply, hP, map_zero]

private lemma exists_forall_ker_le
  (hxt : ∀ v i, t v (x (v + 1) i) = x v i)
  (hxker : ∀ N : ℕ, ∃ v, RingHom.ker (φ 𝓞 p R x v) ≤
    (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p)))) ^ N) (N : ℕ) :
  ∃ v₀, ∀ v, v₀ ≤ v → RingHom.ker (φ 𝓞 p R x v) ≤
    (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p)))) ^ N := by
  obtain ⟨v₀, hv₀⟩ := hxker N
  exact ⟨v₀, fun v hv => (ker_φ_anti 𝓞 hxt hv).trans hv₀⟩

end One

section Two

variable (𝓞 : Type u) [CommRing 𝓞] (p : ℕ) (R : ℕ → Type v) [∀ v, CommRing (R v)] [∀ v, Algebra 𝓞 (R v)] (R' : ℕ → Type v) [∀ v, CommRing (R' v)] [∀ v, Algebra 𝓞 (R' v)]

private lemma tmul_one_mem_radical (v : ℕ) {a : R v} (ha : a ∈ (Ideal.span {(p : R v)}).radical) :
  a ⊗ₜ[𝓞] (1 : R' v) ∈ (Ideal.span {(p : R v ⊗[𝓞] R' v)}).radical := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
  refine ⟨n, ?_⟩
  have hmul : (c * (p : R v)) ⊗ₜ[𝓞] (1 : R' v) = (c ⊗ₜ[𝓞] (1 : R' v)) * ((p : R v) ⊗ₜ[𝓞] (1 : R' v)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [Algebra.TensorProduct.tmul_pow, one_pow, ← hc, hmul,
    ← Algebra.TensorProduct.natCast_def]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private lemma one_tmul_mem_radical (v : ℕ) {a : R' v} (ha : a ∈ (Ideal.span {(p : R' v)}).radical) :
  (1 : R v) ⊗ₜ[𝓞] a ∈ (Ideal.span {(p : R v ⊗[𝓞] R' v)}).radical := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
  refine ⟨n, ?_⟩
  have hmul : (1 : R v) ⊗ₜ[𝓞] (c * (p : R' v)) = ((1 : R v) ⊗ₜ[𝓞] c) * ((1 : R v) ⊗ₜ[𝓞] (p : R' v)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [Algebra.TensorProduct.tmul_pow, one_pow, ← hc, hmul,
    ← Algebra.TensorProduct.natCast_def']
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end Two

section Three

variable (𝓞 : Type u) [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)] (R : ℕ → Type v) [∀ v, CommRing (R v)] [∀ v, Algebra 𝓞 (R v)] (R' : ℕ → Type v) [∀ v, CommRing (R' v)] [∀ v, Algebra 𝓞 (R' v)] {σ : Type w} (x : ∀ v, σ → R v) {σ' : Type w'} (x' : ∀ v, σ' → R' v)

private noncomputable abbrev Φ (v : ℕ) :
  MvPolynomial (σ ⊕ σ') (ZMod p) →ₐ[ZMod p] ZMod p ⊗[𝓞] (R v ⊗[𝓞] R' v) :=
  MvPolynomial.aeval fun s => (1 : ZMod p) ⊗ₜ[𝓞]
    Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s

private noncomputable abbrev ι₁ (v : ℕ) : ZMod p ⊗[𝓞] R v →ₐ[ZMod p] ZMod p ⊗[𝓞] (R v ⊗[𝓞] R' v) :=
  Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p))
    (Algebra.TensorProduct.includeLeft : R v →ₐ[𝓞] R v ⊗[𝓞] R' v)

private noncomputable abbrev ι₂ (v : ℕ) : ZMod p ⊗[𝓞] R' v →ₐ[ZMod p] ZMod p ⊗[𝓞] (R v ⊗[𝓞] R' v) :=
  Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p))
    (Algebra.TensorProduct.includeRight : R' v →ₐ[𝓞] R v ⊗[𝓞] R' v)

variable {p R R' x x'}

private lemma Φ_rename_inl (v : ℕ) (P : MvPolynomial σ (ZMod p)) :
  Φ 𝓞 p R R' x x' v (MvPolynomial.rename Sum.inl P) = ι₁ 𝓞 p R R' v (φ 𝓞 p R x v P) := by
  have h : (Φ 𝓞 p R R' x x' v).comp (MvPolynomial.rename Sum.inl) = (ι₁ 𝓞 p R R' v).comp (φ 𝓞 p R x v) :=
    MvPolynomial.algHom_ext fun i => by
      simp only [AlgHom.comp_apply, MvPolynomial.rename_X, MvPolynomial.aeval_X, Sum.elim_inl,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply]
  refine AlgHom.congr_fun h P

private lemma Φ_rename_inr (v : ℕ) (P : MvPolynomial σ' (ZMod p)) :
  Φ 𝓞 p R R' x x' v (MvPolynomial.rename Sum.inr P) = ι₂ 𝓞 p R R' v (φ 𝓞 p R' x' v P) := by
  have h : (Φ 𝓞 p R R' x x' v).comp (MvPolynomial.rename Sum.inr) = (ι₂ 𝓞 p R R' v).comp (φ 𝓞 p R' x' v) :=
    MvPolynomial.algHom_ext fun i => by
      simp only [AlgHom.comp_apply, MvPolynomial.rename_X, MvPolynomial.aeval_X, Sum.elim_inr,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply]
  refine AlgHom.congr_fun h P

private lemma Φ_surjective
  (hxsurj : ∀ v, Surjective (φ 𝓞 p R x v))
  (hxsurj' : ∀ v, Surjective (φ 𝓞 p R' x' v)) (v : ℕ) : Surjective (Φ 𝓞 p R R' x x' v) := by
  have hmem : ∀ z, z ∈ (Φ 𝓞 p R R' x x' v).range := by
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    ·
      intro c w
      have hcw : c ⊗ₜ[𝓞] w = c • ((1 : ZMod p) ⊗ₜ[𝓞] w) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hcw]
      refine Subalgebra.smul_mem _ ?_ c
      clear hcw
      refine TensorProduct.inductionOn w ?_ ?_
      ·
        intro r r'
        have hrr : (1 : ZMod p) ⊗ₜ[𝓞] (r ⊗ₜ[𝓞] r') =
            ((1 : ZMod p) ⊗ₜ[𝓞] (r ⊗ₜ[𝓞] (1 : R' v))) * ((1 : ZMod p) ⊗ₜ[𝓞] ((1 : R v) ⊗ₜ[𝓞] r')) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [hrr]
        refine Subalgebra.mul_mem _ ?_ ?_
        ·
          obtain ⟨P, hP⟩ := hxsurj v ((1 : ZMod p) ⊗ₜ[𝓞] r)
          refine ⟨MvPolynomial.rename Sum.inl P, ?_⟩
          change Φ 𝓞 p R R' x x' v _ = _
          rw [Φ_rename_inl 𝓞, hP, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
            Algebra.TensorProduct.includeLeft_apply]
        ·
          obtain ⟨P, hP⟩ := hxsurj' v ((1 : ZMod p) ⊗ₜ[𝓞] r')
          refine ⟨MvPolynomial.rename Sum.inr P, ?_⟩
          change Φ 𝓞 p R R' x x' v _ = _
          rw [Φ_rename_inr 𝓞, hP, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
            Algebra.TensorProduct.includeRight_apply]
      ·
        intro a b ha hb
        rw [TensorProduct.tmul_add]
        exact Subalgebra.add_mem _ ha hb
    ·
      intro a b ha hb
      exact Subalgebra.add_mem _ ha hb
  intro z
  obtain ⟨P, hP⟩ := hmem z
  exact ⟨P, hP⟩

end Three

section Four

variable (𝓞 : Type u) [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)] (R : ℕ → Type v) [∀ v, CommRing (R v)] [∀ v, Algebra 𝓞 (R v)] (R' : ℕ → Type v) [∀ v, CommRing (R' v)] [∀ v, Algebra 𝓞 (R' v)] {σ : Type w} (x : ∀ v, σ → R v) {σ' : Type w'} (x' : ∀ v, σ' → R' v)

private lemma ker_Φ_le
  {N v : ℕ}
  (hs : Surjective (φ 𝓞 p R x v)) (hs' : Surjective (φ 𝓞 p R' x' v))
  (hv : RingHom.ker (φ 𝓞 p R x v) ≤
    (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p)))) ^ N)
  (hv' : RingHom.ker (φ 𝓞 p R' x' v) ≤
    (Ideal.span (Set.range (MvPolynomial.X : σ' → MvPolynomial σ' (ZMod p)))) ^ N) :
  RingHom.ker (Φ 𝓞 p R R' x x' v) ≤
    (Ideal.span (Set.range (MvPolynomial.X : σ ⊕ σ' → MvPolynomial (σ ⊕ σ') (ZMod p)))) ^ N := by
  classical
  set 𝔛 : Ideal (MvPolynomial (σ ⊕ σ') (ZMod p)) :=
    Ideal.span (Set.range (MvPolynomial.X : σ ⊕ σ' → MvPolynomial (σ ⊕ σ') (ZMod p))) with h𝔛
  let θ : MvPolynomial σ (ZMod p) →ₐ[ZMod p] MvPolynomial (σ ⊕ σ') (ZMod p) ⧸ 𝔛 ^ N :=
    (Ideal.Quotient.mkₐ (ZMod p) (𝔛 ^ N)).comp (MvPolynomial.rename Sum.inl)
  let θ' : MvPolynomial σ' (ZMod p) →ₐ[ZMod p] MvPolynomial (σ ⊕ σ') (ZMod p) ⧸ 𝔛 ^ N :=
    (Ideal.Quotient.mkₐ (ZMod p) (𝔛 ^ N)).comp (MvPolynomial.rename Sum.inr)
  have hθ : ∀ P ∈ RingHom.ker (φ 𝓞 p R x v), θ P = 0 := by
    intro P hP
    have h2 := Ideal.mem_map_of_mem (MvPolynomial.rename (Sum.inl : σ → σ ⊕ σ')) (hv hP)
    rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp] at h2
    have h3 : Ideal.span (Set.range (⇑(MvPolynomial.rename (Sum.inl : σ → σ ⊕ σ')) ∘
        (MvPolynomial.X : σ → MvPolynomial σ (ZMod p)))) ≤ 𝔛 := by
      rw [h𝔛]
      refine Ideal.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨Sum.inl i, (MvPolynomial.rename_X _ i).symm⟩
    change Ideal.Quotient.mk (𝔛 ^ N) (MvPolynomial.rename Sum.inl P) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_right_mono h3 N h2)
  have hθ' : ∀ P ∈ RingHom.ker (φ 𝓞 p R' x' v), θ' P = 0 := by
    intro P hP
    have h2 := Ideal.mem_map_of_mem (MvPolynomial.rename (Sum.inr : σ' → σ ⊕ σ')) (hv' hP)
    rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp] at h2
    have h3 : Ideal.span (Set.range (⇑(MvPolynomial.rename (Sum.inr : σ' → σ ⊕ σ')) ∘
        (MvPolynomial.X : σ' → MvPolynomial σ' (ZMod p)))) ≤ 𝔛 := by
      rw [h𝔛]
      refine Ideal.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨Sum.inr i, (MvPolynomial.rename_X _ i).symm⟩
    change Ideal.Quotient.mk (𝔛 ^ N) (MvPolynomial.rename Sum.inr P) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_right_mono h3 N h2)
  let ψ : ZMod p ⊗[𝓞] R v →ₐ[ZMod p] MvPolynomial (σ ⊕ σ') (ZMod p) ⧸ 𝔛 ^ N :=
    (Ideal.Quotient.liftₐ (RingHom.ker (φ 𝓞 p R x v)) θ hθ).comp
      (Ideal.quotientKerAlgEquivOfSurjective hs).symm.toAlgHom
  let ψ' : ZMod p ⊗[𝓞] R' v →ₐ[ZMod p] MvPolynomial (σ ⊕ σ') (ZMod p) ⧸ 𝔛 ^ N :=
    (Ideal.Quotient.liftₐ (RingHom.ker (φ 𝓞 p R' x' v)) θ' hθ').comp
      (Ideal.quotientKerAlgEquivOfSurjective hs').symm.toAlgHom
  have hψ : ∀ P, ψ (φ 𝓞 p R x v P) = θ P := by
    intro P
    change Ideal.Quotient.liftₐ _ θ hθ ((Ideal.quotientKerAlgEquivOfSurjective hs).symm (φ 𝓞 p R x v P)) = θ P
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
    rfl
  have hψ' : ∀ P, ψ' (φ 𝓞 p R' x' v P) = θ' P := by
    intro P
    change Ideal.Quotient.liftₐ _ θ' hθ' ((Ideal.quotientKerAlgEquivOfSurjective hs').symm (φ 𝓞 p R' x' v P)) = θ' P
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
    rfl
  let gR : R v →ₐ[𝓞] MvPolynomial (σ ⊕ σ') (ZMod p) ⧸ 𝔛 ^ N :=
    (ψ.restrictScalars 𝓞).comp (Algebra.TensorProduct.includeRight : R v →ₐ[𝓞] ZMod p ⊗[𝓞] R v)
  let gR' : R' v →ₐ[𝓞] MvPolynomial (σ ⊕ σ') (ZMod p) ⧸ 𝔛 ^ N :=
    (ψ'.restrictScalars 𝓞).comp (Algebra.TensorProduct.includeRight : R' v →ₐ[𝓞] ZMod p ⊗[𝓞] R' v)
  let g : R v ⊗[𝓞] R' v →ₐ[𝓞] MvPolynomial (σ ⊕ σ') (ZMod p) ⧸ 𝔛 ^ N :=
    Algebra.TensorProduct.lift gR gR' fun _ _ => Commute.all _ _
  let Ψ : ZMod p ⊗[𝓞] (R v ⊗[𝓞] R' v) →ₐ[ZMod p] MvPolynomial (σ ⊕ σ') (ZMod p) ⧸ 𝔛 ^ N :=
    Algebra.TensorProduct.lift (Algebra.ofId (ZMod p) _) g fun _ _ => Commute.all _ _
  have hgR : ∀ i, gR (x v i) = Ideal.Quotient.mk (𝔛 ^ N) (MvPolynomial.X (Sum.inl i)) := by
    intro i
    change ψ ((1 : ZMod p) ⊗ₜ[𝓞] x v i) = _
    rw [← MvPolynomial.aeval_X (R := ZMod p) (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) i]
    change ψ (φ 𝓞 p R x v (MvPolynomial.X i)) = _
    rw [hψ]
    change Ideal.Quotient.mk (𝔛 ^ N) (MvPolynomial.rename Sum.inl (MvPolynomial.X i)) = _
    rw [MvPolynomial.rename_X]
  have hgR' : ∀ i, gR' (x' v i) = Ideal.Quotient.mk (𝔛 ^ N) (MvPolynomial.X (Sum.inr i)) := by
    intro i
    change ψ' ((1 : ZMod p) ⊗ₜ[𝓞] x' v i) = _
    rw [← MvPolynomial.aeval_X (R := ZMod p) (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x' v i) i]
    change ψ' (φ 𝓞 p R' x' v (MvPolynomial.X i)) = _
    rw [hψ']
    change Ideal.Quotient.mk (𝔛 ^ N) (MvPolynomial.rename Sum.inr (MvPolynomial.X i)) = _
    rw [MvPolynomial.rename_X]
  have hcomp : Ψ.comp (Φ 𝓞 p R R' x x' v) = Ideal.Quotient.mkₐ (ZMod p) (𝔛 ^ N) := by
    refine MvPolynomial.algHom_ext fun s => ?_
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    cases s with
    | inl i =>
      rw [Sum.elim_inl]
      change Algebra.TensorProduct.lift (Algebra.ofId (ZMod p) _) g _ ((1 : ZMod p) ⊗ₜ[𝓞] (x v i ⊗ₜ[𝓞] (1 : R' v))) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      change Algebra.TensorProduct.lift gR gR' _ (x v i ⊗ₜ[𝓞] (1 : R' v)) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one, hgR]
    | inr i =>
      rw [Sum.elim_inr]
      change Algebra.TensorProduct.lift (Algebra.ofId (ZMod p) _) g _ ((1 : ZMod p) ⊗ₜ[𝓞] ((1 : R v) ⊗ₜ[𝓞] x' v i)) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      change Algebra.TensorProduct.lift gR gR' _ ((1 : R v) ⊗ₜ[𝓞] x' v i) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul, hgR']
  intro P hP
  rw [RingHom.mem_ker] at hP
  have h : Ideal.Quotient.mkₐ (ZMod p) (𝔛 ^ N) P = 0 := by
    rw [← hcomp, AlgHom.comp_apply, hP, map_zero]
  rwa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h

end Four


/--
[Algebra_TensorProduct_specialFibre_coordinates_sumElim_tmul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_specialFibre_coordinates_sumElim_tmul.lean)
-/
@[path]
private lemma main
  {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  (R : ℕ → Type v) [∀ v, CommRing (R v)] [∀ v, Algebra 𝓞 (R v)]
  (t : ∀ v, R (v + 1) →ₐ[𝓞] R v)
  {σ : Type w} [Finite σ] (x : ∀ v, σ → R v) (hxt : ∀ v i, t v (x (v + 1) i) = x v i)
  (hxrad : ∀ v i, x v i ∈ (Ideal.span {(p : R v)}).radical)
  (hxsurj : ∀ v, Function.Surjective
    (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
      MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R v)))
  (hxker : ∀ N : ℕ, ∃ v, RingHom.ker
    (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
      MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R v)) ≤
    (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p)))) ^ N)
  (R' : ℕ → Type v) [∀ v, CommRing (R' v)] [∀ v, Algebra 𝓞 (R' v)]
  (t' : ∀ v, R' (v + 1) →ₐ[𝓞] R' v)
  {σ' : Type w'} [Finite σ'] (x' : ∀ v, σ' → R' v) (hxt' : ∀ v i, t' v (x' (v + 1) i) = x' v i)
  (hxrad' : ∀ v i, x' v i ∈ (Ideal.span {(p : R' v)}).radical)
  (hxsurj' : ∀ v, Function.Surjective
    (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x' v i) :
      MvPolynomial σ' (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R' v)))
  (hxker' : ∀ N : ℕ, ∃ v, RingHom.ker
    (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x' v i) :
      MvPolynomial σ' (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R' v)) ≤
    (Ideal.span (Set.range (MvPolynomial.X : σ' → MvPolynomial σ' (ZMod p)))) ^ N) :
  (∀ v s, Algebra.TensorProduct.map (t v) (t' v)
      (Sum.elim (fun i => x (v + 1) i ⊗ₜ[𝓞] (1 : R' (v + 1)))
        (fun i => (1 : R (v + 1)) ⊗ₜ[𝓞] x' (v + 1) i) s) =
    Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s) ∧
  (∀ v s, Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s ∈
    (Ideal.span {(p : R v ⊗[𝓞] R' v)}).radical) ∧
  (∀ v, Function.Surjective
    (MvPolynomial.aeval (fun s => (1 : ZMod p) ⊗ₜ[𝓞]
        Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s) :
      MvPolynomial (σ ⊕ σ') (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R v ⊗[𝓞] R' v))) ∧
  (∀ N : ℕ, ∃ v, RingHom.ker
    (MvPolynomial.aeval (fun s => (1 : ZMod p) ⊗ₜ[𝓞]
        Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s) :
      MvPolynomial (σ ⊕ σ') (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R v ⊗[𝓞] R' v)) ≤
    (Ideal.span (Set.range
      (MvPolynomial.X : σ ⊕ σ' → MvPolynomial (σ ⊕ σ') (ZMod p)))) ^ N) := by
  refine ⟨?_, ?_, fun v => Φ_surjective 𝓞 hxsurj hxsurj' v, fun N => ?_⟩
  ·
    rintro v (i | i)
    · simp only [Sum.elim_inl, Algebra.TensorProduct.map_tmul, map_one, hxt]
    · simp only [Sum.elim_inr, Algebra.TensorProduct.map_tmul, map_one, hxt']
  ·
    rintro v (i | i)
    · exact tmul_one_mem_radical 𝓞 p R R' v (hxrad v i)
    · exact one_tmul_mem_radical 𝓞 p R R' v (hxrad' v i)
  ·
    obtain ⟨v₁, hv₁⟩ := exists_forall_ker_le 𝓞 hxt hxker N
    obtain ⟨v₂, hv₂⟩ := exists_forall_ker_le 𝓞 hxt' hxker' N
    exact ⟨max v₁ v₂, ker_Φ_le 𝓞 p R R' x x' (hxsurj _) (hxsurj' _) (hv₁ _ (le_max_left _ _))
      (hv₂ _ (le_max_right _ _))⟩


-- created on 2026-10-13
