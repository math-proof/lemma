import Mathlib
import sympy.Basic
open scoped TensorProduct


private abbrev spanG
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} (g : ι → T) (S₀ : Subalgebra ℤ S) :
  Submodule S₀ T :=
  Submodule.span S₀ (Set.range g)

private lemma g_mem_spanG
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} {g : ι → T} {S₀ : Subalgebra ℤ S}
  (i : ι) :
-- imply
  g i ∈ spanG g S₀ :=
  Submodule.subset_span ⟨i, rfl⟩

private lemma mem_spanG_of_coeff
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
-- given
  (hσ : ∀ t, ∑ i, σ t i • g i = t)
  {t : T} (ht : ∀ k, σ t k ∈ S₀) :
-- imply
  t ∈ spanG g S₀ := by
-- proof
  rw [← hσ t]
  refine Submodule.sum_mem _ fun k _ => ?_
  have : σ t k • g k = (⟨σ t k, ht k⟩ : S₀) • g k := rfl
  rw [this]
  apply Submodule.smul_mem _ _ (g_mem_spanG k)

private lemma coeff_mem_of_mem_spanG
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
-- given
  (hgc : ∀ i k, σ (g i) k ∈ S₀)
  {t : T} (ht : t ∈ spanG g S₀)
  (k : ι) :
-- imply
  σ t k ∈ S₀ := by
-- proof
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    apply hgc i k
  | zero =>
    simp
  | add x y _ _ hx hy =>
    rw [map_add, Pi.add_apply]
    apply add_mem hx hy
  | smul a x _ hx =>
    have : (a • x : T) = (a : S) • x := rfl
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul]
    apply mul_mem a.2 hx

private lemma one_mem_spanG
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
-- given
  (hσ : ∀ t, ∑ i, σ t i • g i = t)
  (h0 : ∀ k, σ 1 k ∈ S₀) :
-- imply
  (1 : T) ∈ spanG g S₀ :=
  mem_spanG_of_coeff hσ h0

private lemma mul_mem_spanG
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
  (hσ : ∀ t, ∑ i, σ t i • g i = t)
  (hm : ∀ i j k, σ (g i * g j) k ∈ S₀)
  (x y : T)
-- given
  (hx : x ∈ spanG g S₀) (hy : y ∈ spanG g S₀) :
-- imply
  x * y ∈ spanG g S₀ := by
-- proof
  induction hx using Submodule.span_induction generalizing y with
  | mem x hx' =>
    obtain ⟨i, rfl⟩ := hx'
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨j, rfl⟩ := hy'
      apply mem_spanG_of_coeff hσ (hm i j)
    | zero =>
      simp
    | add y z _ _ hy hz =>
      rw [mul_add]
      apply add_mem hy hz
    | smul a y _ hy' =>
      rw [mul_smul_comm]
      apply Submodule.smul_mem _ _ hy'
  | zero =>
    simp
  | add x x' _ _ hx hx' =>
    rw [add_mul]
    apply add_mem (hx y hy) (hx' y hy)
  | smul a x _ hx =>
    rw [smul_mul_assoc]
    apply Submodule.smul_mem _ _ (hx y hy)

private def model
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι] (g : ι → T) (σ : T →ₗ[S] (ι → S)) (S₀ : Subalgebra ℤ S)
  (hσ : ∀ t, ∑ i, σ t i • g i = t) (h1 : ∀ k, σ 1 k ∈ S₀)
  (hm : ∀ i j k, σ (g i * g j) k ∈ S₀) :
  Subalgebra S₀ T :=
  (spanG g S₀).toSubalgebra (one_mem_spanG (g := g) (σ := σ) hσ h1)
    (mul_mem_spanG (g := g) (σ := σ) hσ hm)

private lemma model_toSubmodule
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι] (g : ι → T) (σ : T →ₗ[S] (ι → S)) (S₀ : Subalgebra ℤ S)
  (hσ : ∀ t, ∑ i, σ t i • g i = t) (h1 : ∀ k, σ 1 k ∈ S₀)
  (hm : ∀ i j k, σ (g i * g j) k ∈ S₀) :
-- imply
  Subalgebra.toSubmodule (model g σ S₀ hσ h1 hm) = spanG g S₀ :=
  Submodule.toSubalgebra_toSubmodule _ _ _

private def g'
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} (g : ι → T) (S₀ : Subalgebra ℤ S) (i : ι) :
  spanG g S₀ :=
  ⟨g i, g_mem_spanG i⟩

private lemma coe_g'
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} {g : ι → T} {S₀ : Subalgebra ℤ S} (i : ι) :
-- imply
  ((g' g S₀ i : spanG g S₀) : T) = g i :=
  rfl

private noncomputable def pi0
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι] (g : ι → T) (S₀ : Subalgebra ℤ S) :
  (ι → S₀) →ₗ[S₀] spanG g S₀ :=
  Fintype.linearCombination S₀ (g' g S₀)

private lemma pi0_apply
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {S₀ : Subalgebra ℤ S}
  (v : ι → S₀) :
-- imply
  pi0 g S₀ v = ∑ i, v i • g' g S₀ i :=
  Fintype.linearCombination_apply _ _ _

private lemma coe_pi0
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {S₀ : Subalgebra ℤ S}
  (v : ι → S₀) :
-- imply
  ((pi0 g S₀ v : spanG g S₀) : T) = ∑ i, (v i : S) • g i := by
-- proof
  rw [pi0_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl

private noncomputable def sigma0
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} (g : ι → T) (σ : T →ₗ[S] (ι → S)) (S₀ : Subalgebra ℤ S)
  (hgc : ∀ i k, σ (g i) k ∈ S₀) :
  spanG g S₀ →ₗ[S₀] (ι → S₀) where
  toFun x := fun k => ⟨σ x k, coeff_mem_of_mem_spanG hgc x.2 k⟩
  map_add' := by
    intro x y
    funext k
    apply Subtype.ext
    change σ ((x : T) + y) k = σ x k + σ y k
    rw [map_add, Pi.add_apply]
  map_smul' := by
    intro a x
    funext k
    apply Subtype.ext
    change σ ((a : S) • (x : T)) k = (a : S) * σ x k
    rw [map_smul, Pi.smul_apply, smul_eq_mul]

private lemma coe_sigma0_apply
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
  (hgc : ∀ i k, σ (g i) k ∈ S₀) (x : spanG g S₀) (k : ι) :
-- imply
  ((sigma0 g σ S₀ hgc x k : S₀) : S) = σ x k :=
  rfl

private lemma pi0_sigma0
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
-- given
  (hσ : ∀ t, ∑ i, σ t i • g i = t)
  (hgc : ∀ i k, σ (g i) k ∈ S₀)
  (x : spanG g S₀) :
-- imply
  pi0 g S₀ (sigma0 g σ S₀ hgc x) = x := by
-- proof
  apply Subtype.ext
  rw [coe_pi0]
  simp only [coe_sigma0_apply]
  exact hσ x

private lemma pi0_comp_sigma0
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
-- given
  (hσ : ∀ t, ∑ i, σ t i • g i = t)
  (hgc : ∀ i k, σ (g i) k ∈ S₀) :
-- imply
  (pi0 g S₀).comp (sigma0 g σ S₀ hgc) = LinearMap.id :=
  LinearMap.ext fun x => pi0_sigma0 hσ hgc x

private lemma projective_spanG
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
-- given
  (hσ : ∀ t, ∑ i, σ t i • g i = t)
  (hgc : ∀ i k, σ (g i) k ∈ S₀) :
-- imply
  Module.Projective S₀ (spanG g S₀) :=
  Module.Projective.of_split (sigma0 g σ S₀ hgc) (pi0 g S₀) (pi0_comp_sigma0 hσ hgc)

private lemma finite_spanG
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Finite ι]
  {g : ι → T} {S₀ : Subalgebra ℤ S} :
-- imply
  Module.Finite S₀ (spanG g S₀) :=
  Module.Finite.span_of_finite S₀ (Set.finite_range g)

private lemma free_spanG
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} {g : ι → T} {S₀ : Subalgebra ℤ S}
-- given
  (hli : LinearIndependent S g) :
-- imply
  Module.Free S₀ (spanG g S₀) :=
  Module.Free.of_basis (Module.Basis.span (hli.restrict_scalars' S₀))

private noncomputable def psi
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι] (g : ι → T) (σ : T →ₗ[S] (ι → S)) (S₀ : Subalgebra ℤ S) :
  T →ₗ[S] S ⊗[S₀] spanG g S₀ :=
  ∑ k : ι, (LinearMap.toSpanSingleton S (S ⊗[S₀] spanG g S₀) (1 ⊗ₜ g' g S₀ k)).comp
    ((LinearMap.proj k).comp σ)

private lemma psi_apply
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
  (t : T) :
-- imply
  psi g σ S₀ t = ∑ k : ι, σ t k ⊗ₜ[S₀] g' g S₀ k := by
-- proof
  rw [psi, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
    LinearMap.proj_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private noncomputable def theta
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} (g : ι → T) (S₀ : Subalgebra ℤ S) :
  S ⊗[S₀] spanG g S₀ →ₗ[S] T :=
  ((spanG g S₀).subtype).liftBaseChange S

private lemma theta_tmul
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} {g : ι → T} {S₀ : Subalgebra ℤ S}
  (s : S) (x : spanG g S₀) :
-- imply
  theta g S₀ (s ⊗ₜ x) = s • (x : T) :=
  LinearMap.liftBaseChange_tmul _ _ _ _

private lemma sum_tmul_eq_one_tmul
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
-- given
  (hσ : ∀ t, ∑ i, σ t i • g i = t)
  (hgc : ∀ i k, σ (g i) k ∈ S₀)
  (x : spanG g S₀) :
-- imply
  ∑ k : ι, σ x k ⊗ₜ[S₀] g' g S₀ k = (1 : S) ⊗ₜ[S₀] x := by
-- proof
  have hx : ∀ k, σ x k ⊗ₜ[S₀] g' g S₀ k =
      (1 : S) ⊗ₜ[S₀] ((sigma0 g σ S₀ hgc x k) • g' g S₀ k) := by
    intro k
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    change σ x k = ((sigma0 g σ S₀ hgc x k : S₀) : S) * 1
    rw [mul_one]
    rfl
  simp_rw [hx]
  rw [← TensorProduct.tmul_sum, ← pi0_apply, pi0_sigma0 hσ hgc x]

private lemma psi_comp_theta
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
-- given
  (hσ : ∀ t, ∑ i, σ t i • g i = t)
  (hgc : ∀ i k, σ (g i) k ∈ S₀) :
-- imply
  (psi g σ S₀).comp (theta g S₀) = LinearMap.id := by
-- proof
  refine TensorProduct.AlgebraTensorModule.ext fun s x => ?_
  rw [LinearMap.comp_apply, LinearMap.id_apply, theta_tmul, map_smul, psi_apply,
    sum_tmul_eq_one_tmul hσ hgc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private lemma theta_injective
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
-- given
  (hσ : ∀ t, ∑ i, σ t i • g i = t)
  (hgc : ∀ i k, σ (g i) k ∈ S₀) :
-- imply
  Function.Injective (theta g S₀) := by
-- proof
  intro a b hab
  have h := LinearMap.congr_fun (psi_comp_theta hσ hgc) a
  have h' := LinearMap.congr_fun (psi_comp_theta hσ hgc) b
  rw [LinearMap.comp_apply, LinearMap.id_apply] at h h'
  rw [← h, ← h', hab]

private lemma theta_surjective
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} {g : ι → T} {S₀ : Subalgebra ℤ S}
-- given
  (hg : Submodule.span S (Set.range g) = ⊤) :
-- imply
  Function.Surjective (theta g S₀) := by
-- proof
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hg, Submodule.span_le]
  intro _ h
  obtain ⟨i, rfl⟩ := h
  refine ⟨1 ⊗ₜ g' g S₀ i, ?_⟩
  rw [theta_tmul, one_smul]
  rfl

private noncomputable def thetaEquiv
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι] (g : ι → T) (σ : T →ₗ[S] (ι → S)) (S₀ : Subalgebra ℤ S)
  (hσ : ∀ t, ∑ i, σ t i • g i = t)
  (hgc : ∀ i k, σ (g i) k ∈ S₀)
  (hg : Submodule.span S (Set.range g) = ⊤) :
  S ⊗[S₀] spanG g S₀ ≃ₗ[S] T :=
  LinearEquiv.ofBijective (theta g S₀) ⟨theta_injective (g := g) (σ := σ) hσ hgc,
    theta_surjective (g := g) hg⟩

private lemma isBaseChange_subtype
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
-- given
  (hσ : ∀ t, ∑ i, σ t i • g i = t)
  (hgc : ∀ i k, σ (g i) k ∈ S₀)
  (hg : Submodule.span S (Set.range g) = ⊤) :
-- imply
  IsBaseChange S ((spanG g S₀).subtype) :=
  IsBaseChange.of_equiv (thetaEquiv g σ S₀ hσ hgc hg) fun x => by
    change theta g S₀ ((1 : S) ⊗ₜ x) = x
    rw [theta_tmul, one_smul]

private lemma isPushout_model
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
-- given
  (hσ : ∀ t, ∑ i, σ t i • g i = t)
  (h0 : ∀ k, σ 1 k ∈ S₀)
  (hm : ∀ i j k, σ (g i * g j) k ∈ S₀)
  (hgc : ∀ i k, σ (g i) k ∈ S₀)
  (hg : Submodule.span S (Set.range g) = ⊤) :
-- imply
  Algebra.IsPushout S₀ S (model g σ S₀ hσ h0 hm) T := by
-- proof
  rw [Algebra.isPushout_iff]
  have : (IsScalarTower.toAlgHom S₀ (model g σ S₀ hσ h0 hm) T).toLinearMap =
      (spanG g S₀).subtype := by
    refine LinearMap.ext fun x => ?_
    rfl
  rw [this]
  apply isBaseChange_subtype hσ hgc hg

private lemma finite_model
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
  (hσ : ∀ t, ∑ i, σ t i • g i = t)
  (h1 : ∀ k, σ 1 k ∈ S₀)
  (hm : ∀ i j k, σ (g i * g j) k ∈ S₀) :
-- imply
  Module.Finite S₀ (model g σ S₀ hσ h1 hm) :=
  finite_spanG (g := g) (S₀ := S₀)

private lemma projective_model
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
-- given
  (hσ : ∀ t, ∑ i, σ t i • g i = t)
  (h0 : ∀ k, σ 1 k ∈ S₀)
  (hm : ∀ i j k, σ (g i * g j) k ∈ S₀)
  (hgc : ∀ i k, σ (g i) k ∈ S₀) :
-- imply
  Module.Projective S₀ (model g σ S₀ hσ h0 hm) :=
  projective_spanG (g := g) (σ := σ) hσ hgc

private lemma free_model
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
  {ι : Type} [Fintype ι]
  {g : ι → T} {σ : T →ₗ[S] (ι → S)} {S₀ : Subalgebra ℤ S}
  (hσ : ∀ t, ∑ i, σ t i • g i = t)
  (h1 : ∀ k, σ 1 k ∈ S₀)
  (hm : ∀ i j k, σ (g i * g j) k ∈ S₀)
-- given
  (hli : LinearIndependent S g) :
-- imply
  Module.Free S₀ (model g σ S₀ hσ h1 hm) :=
  free_spanG (g := g) hli

private lemma pushout_main
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T] [Module.Projective S T]
  {ι : Type} [Finite ι]
  {g : ι → T}
-- given
  (hg : Submodule.span S (Set.range g) = ⊤) :
-- imply
  ∃ c : Finset S, ∀ S₀ : Subalgebra ℤ S, ↑c ⊆ (S₀ : Set S) →
    ∃ T₀ : Subalgebra S₀ T, Subalgebra.toSubmodule T₀ = Submodule.span S₀ (Set.range g) ∧
      Module.Finite S₀ T₀ ∧ Module.Projective S₀ T₀ ∧
      (LinearIndependent S g → Module.Free S₀ T₀) ∧ Algebra.IsPushout S₀ S T₀ T := by
-- proof
  classical
  cases nonempty_fintype ι
  have hsurj : Function.Surjective (Fintype.linearCombination S g) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hg]
  obtain ⟨σ, hσ'⟩ :=
    Module.projective_lifting_property (Fintype.linearCombination S g) LinearMap.id hsurj
  have hσ : ∀ t, ∑ i, σ t i • g i = t := fun t => by
    have := LinearMap.congr_fun hσ' t
    rwa [LinearMap.comp_apply, Fintype.linearCombination_apply, LinearMap.id_apply] at this
  let c : Finset S := ((Finset.univ.image fun k : ι => σ 1 k) ∪
    (Finset.univ.image fun p : (ι × ι) × ι => σ (g p.1.1 * g p.1.2) p.2)) ∪
    (Finset.univ.image fun p : ι × ι => σ (g p.1) p.2)
  refine ⟨c, fun S₀ hc => ?_⟩
  have h1 : ∀ k, σ 1 k ∈ S₀ := fun k => hc (by simp only [c, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union, Set.mem_range]; refine Or.inl (Or.inl ⟨k, rfl⟩))
  have hm : ∀ i j k, σ (g i * g j) k ∈ S₀ := fun i j k => hc (by simp only [c, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union, Set.mem_range]; refine Or.inl (Or.inr ⟨((i, j), k), rfl⟩))
  have hgc : ∀ i k, σ (g i) k ∈ S₀ := fun i k => hc (by simp only [c, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union, Set.mem_range]; refine Or.inr ⟨(i, k), rfl⟩)
  exact ⟨model g σ S₀ hσ h1 hm, model_toSubmodule g σ S₀ hσ h1 hm,
    finite_model (g := g) (σ := σ) hσ h1 hm,
    projective_model (g := g) (σ := σ) hσ h1 hm hgc,
    fun hli => free_model (g := g) (σ := σ) hσ h1 hm hli,
    isPushout_model (g := g) (σ := σ) hσ h1 hm hgc hg⟩


/--
[Algebra_exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top.lean)
-/
@[path]
private lemma main
  {S T : Type} [CommRing S] [CommRing T] [Algebra S T] [Module.Projective S T]
  {ι : Type} [Finite ι]
  {g : ι → T}
-- given
  (hg : Submodule.span S (Set.range g) = ⊤) :
-- imply
  ∃ c : Finset S, ∀ S₀ : Subalgebra ℤ S, ↑c ⊆ (S₀ : Set S) →
    ∃ T₀ : Subalgebra S₀ T, Subalgebra.toSubmodule T₀ = Submodule.span S₀ (Set.range g) ∧
      Module.Finite S₀ T₀ ∧ Module.Projective S₀ T₀ ∧
      (LinearIndependent S g → Module.Free S₀ T₀) ∧ Algebra.IsPushout S₀ S T₀ T :=
  pushout_main (g := g) hg


-- created on 2026-10-13
