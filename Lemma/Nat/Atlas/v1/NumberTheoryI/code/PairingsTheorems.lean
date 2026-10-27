import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.PairingsTheorems.Part3
open Submodule LinearMap Module


/--
[dualLattice_eq_dualSubmodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma dualLattice_eq_dualSubmodule
  {φ : V →ₗ[K] V →ₗ[K] K}
  {M : Submodule A V} :
-- imply
  dualLattice A K V φ M = BilinForm.dualSubmodule φ M := by
-- proof
  ext v
  constructor
  · intro hv y hy
    exact Submodule.mem_one.mpr (hv y hy)
  · intro hv y hy
    exact Submodule.mem_one.mp (hv y hy)
section DualBasis
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {ι : Type*} [DecidableEq ι] [Finite ι]

/--
[prop_5_7_existence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma prop_5_7_existence
  [Field K]
  [AddCommGroup V]
  [Module K V]
  {B : V →ₗ[K] V →ₗ[K] K}
  {b : Basis ι K V}
-- given
  (hB : B.Nondegenerate) :
-- imply
  ∃ b' : Basis ι K V, ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 :=
-- proof
  ⟨BilinForm.dualBasis B hB b, fun i j => BilinForm.apply_dualBasis_left hB b i j⟩

/--
[prop_5_7_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma prop_5_7_uniqueness
  [Field K]
  [AddCommGroup V]
  [Module K V]
  {B : V →ₗ[K] V →ₗ[K] K}
  {b : Basis ι K V}
  {b₁ b₂ : Basis ι K V}
-- given
  (hB : B.Nondegenerate)
  (h₁ : ∀ i j, B (b₁ i) (b j) = if j = i then 1 else 0)
  (h₂ : ∀ i j, B (b₂ i) (b j) = if j = i then 1 else 0) :
-- imply
  ⇑b₁ = ⇑b₂ := by
-- proof
  rw [← (BilinForm.dualBasis_eq_iff hB b (⇑b₁)).mpr h₁]
  rw [← (BilinForm.dualBasis_eq_iff hB b (⇑b₂)).mpr h₂]
end DualBasis
section DualBasisGeneral
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
  {ι : Type*} [DecidableEq ι] [Finite ι]

/--
[dualBasis_inM_of_perfectPairing_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma dualBasis_inM_of_perfectPairing_apply
  [CommRing A]
  [AddCommGroup M]
  [Module A M]
  {B : M →ₗ[A] M →ₗ[A] A}
  [B.IsPerfPair]
  {b : Basis ι A M}
  {i j : ι} :
-- imply
  B (dualBasis_inM_of_perfectPairing B b i) (b j) = if j = i then 1 else 0 := by
-- proof
  unfold dualBasis_inM_of_perfectPairing
  rw [Basis.map_apply]
  have : B (B.toPerfPair.symm (b.dualBasis i)) (b j) = b.dualBasis i (b j) := by
    rw [← toPerfPair_apply, LinearEquiv.apply_symm_apply]
  rw [this]
  exact b.dualBasis_apply_self i j

/--
[prop_5_7_existence_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma prop_5_7_existence_general
  [CommRing A]
  [AddCommGroup M]
  [Module A M]
  {B : M →ₗ[A] M →ₗ[A] A}
  [B.IsPerfPair]
  {b : Basis ι A M} :
-- imply
  ∃ b' : Basis ι A M, ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 :=
-- proof
  ⟨dualBasis_inM_of_perfectPairing B b,
    fun i j => dualBasis_inM_of_perfectPairing_apply B b i j⟩

/--
[prop_5_7_uniqueness_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma prop_5_7_uniqueness_general
  [CommRing A]
  [AddCommGroup M]
  [Module A M]
  {B : M →ₗ[A] M →ₗ[A] A}
  [B.IsPerfPair]
  {b : Basis ι A M}
  {b₁ b₂ : Basis ι A M}
-- given
  (h₁ : ∀ i j, B (b₁ i) (b j) = if j = i then 1 else 0)
  (h₂ : ∀ i j, B (b₂ i) (b j) = if j = i then 1 else 0) :
-- imply
  ⇑b₁ = ⇑b₂ := by
-- proof
  funext i
  apply B.toPerfPair.injective
  apply b.ext
  intro j
  simp only [toPerfPair_apply]
  rw [h₁ i j, h₂ i j]
end DualBasisGeneral
section DualLatticeLattice
variable
  {A : Type*} [CommRing A] [IsDomain A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

/--
[thm_5_12_dualSubmodule_free_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma thm_5_12_dualSubmodule_free_lattice
  [DecidableEq ι]
  [Finite ι]
  {B : V →ₗ[K] V →ₗ[K] K}
  {b : Basis ι K V}
-- given
  (hB : B.Nondegenerate) :
-- imply
  BilinForm.dualSubmodule B (span A (Set.range b)) = span A (Set.range (BilinForm.dualBasis B hB b)) :=
-- proof
  BilinForm.dualSubmodule_span_of_basis B hB b

/--
[thm_5_12_fg_key](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma thm_5_12_fg_key
  [DecidableEq ι]
  [Finite ι]
  {B : V →ₗ[K] V →ₗ[K] K}
  {b : Basis ι K V}
  {M : Submodule A V}
-- given
  (hB : B.Nondegenerate)
  (hbM : span A (Set.range b) ≤ M) :
-- imply
  BilinForm.dualSubmodule B M ≤ span A (Set.range (BilinForm.dualBasis B hB b)) := by
-- proof
  rw [← BilinForm.dualSubmodule_span_of_basis B hB b]
  exact dualSubmodule_antitone B hbM

/--
[cor_5_13_directSumBilinForm_nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma cor_5_13_directSumBilinForm_nondegenerate
  [Field K]
  [AddCommGroup V₁]
  [Module K V₁]
  [AddCommGroup V₂]
  [Module K V₂]
  {B₁ : V₁ →ₗ[K] V₁ →ₗ[K] K}
  {B₂ : V₂ →ₗ[K] V₂ →ₗ[K] K}
-- given
  (hB₁ : B₁.Nondegenerate)
  (hB₂ : B₂.Nondegenerate) :
-- imply
  (directSumBilinForm B₁ B₂).Nondegenerate := by
-- proof
  constructor
  · intro ⟨x₁, x₂⟩ h
    have h1 : x₁ = 0 := by
      apply hB₁.1
      intro y₁
      have := h (y₁, 0)
      simp [directSumBilinForm, LinearMap.mk₂_apply] at this
      exact this
    have h2 : x₂ = 0 := by
      apply hB₂.1
      intro y₂
      have := h (0, y₂)
      simp [directSumBilinForm, LinearMap.mk₂_apply] at this
      exact this
    exact Prod.ext h1 h2
  · intro ⟨y₁, y₂⟩ h
    have h1 : y₁ = 0 := by
      apply hB₁.2
      intro x₁
      have := h (x₁, 0)
      simp [directSumBilinForm, LinearMap.mk₂_apply] at this
      exact this
    have h2 : y₂ = 0 := by
      apply hB₂.2
      intro x₂
      have := h (0, x₂)
      simp [directSumBilinForm, LinearMap.mk₂_apply] at this
      exact this
    exact Prod.ext h1 h2

/--
[cor_5_13_direct_sum_dual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma cor_5_13_direct_sum_dual
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [AddCommGroup V₁]
  [Module K V₁]
  [Module A V₁]
  [IsScalarTower A K V₁]
  [AddCommGroup V₂]
  [Module K V₂]
  [Module A V₂]
  [IsScalarTower A K V₂]
  {B₁ : V₁ →ₗ[K] V₁ →ₗ[K] K}
  {B₂ : V₂ →ₗ[K] V₂ →ₗ[K] K}
  {M₁ : Submodule A V₁}
  {M₂ : Submodule A V₂} :
-- imply
  BilinForm.dualSubmodule (directSumBilinForm B₁ B₂) (M₁.prod M₂) = (BilinForm.dualSubmodule B₁ M₁).prod (BilinForm.dualSubmodule B₂ M₂) := by
-- proof
  ext ⟨x₁, x₂⟩
  simp only [Submodule.mem_prod, BilinForm.mem_dualSubmodule]
  constructor
  · intro h
    constructor
    · intro m₁ hm₁
      have := h (m₁, 0) (Submodule.mem_prod.mpr ⟨hm₁, M₂.zero_mem⟩)
      simp only [directSumBilinForm, LinearMap.mk₂_apply, map_zero, add_zero] at this
      exact this
    · intro m₂ hm₂
      have := h (0, m₂) (Submodule.mem_prod.mpr ⟨M₁.zero_mem, hm₂⟩)
      simp only [directSumBilinForm, LinearMap.mk₂_apply, map_zero, zero_add] at this
      exact this
  · rintro ⟨h₁, h₂⟩ ⟨m₁, m₂⟩ hm
    simp only [directSumBilinForm, LinearMap.mk₂_apply]
    exact Submodule.add_mem _ (h₁ m₁ (Submodule.mem_prod.mp hm).1) (h₂ m₂ (Submodule.mem_prod.mp hm).2)

/--
[cor_5_13](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma cor_5_13
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [AddCommGroup V₁]
  [Module K V₁]
  [Module A V₁]
  [IsScalarTower A K V₁]
  [AddCommGroup V₂]
  [Module K V₂]
  [Module A V₂]
  [IsScalarTower A K V₂]
  {B₁ : V₁ →ₗ[K] V₁ →ₗ[K] K}
  {B₂ : V₂ →ₗ[K] V₂ →ₗ[K] K}
  {M₁ : Submodule A V₁}
  {M₂ : Submodule A V₂}
-- given
  (hB₁ : B₁.Nondegenerate)
  (hB₂ : B₂.Nondegenerate) :
-- imply
  (directSumBilinForm B₁ B₂).Nondegenerate ∧ BilinForm.dualSubmodule (directSumBilinForm B₁ B₂) (M₁.prod M₂) = (BilinForm.dualSubmodule B₁ M₁).prod (BilinForm.dualSubmodule B₂ M₂) :=
-- proof
  ⟨cor_5_13_directSumBilinForm_nondegenerate B₁ hB₁ B₂ hB₂,
    cor_5_13_direct_sum_dual B₁ B₂ M₁ M₂⟩
section FreeDualLattice
variable
  {A : Type*} [CommRing A]
  {K : Type*} [Field K] [Algebra A K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {ι : Type*} [DecidableEq ι] [Finite ι]

/--
[cor_5_14_dual_basis_property](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma cor_5_14_dual_basis_property
  {B : V →ₗ[K] V →ₗ[K] K}
  {b : Basis ι K V}
  {i j : ι}
-- given
  (hB : B.Nondegenerate) :
-- imply
  B (BilinForm.dualBasis B hB b i) (b j) = if j = i then 1 else 0 :=
-- proof
  BilinForm.apply_dualBasis_left hB b i j

/--
[cor_5_14_dual_basis_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma cor_5_14_dual_basis_unique
  {B : V →ₗ[K] V →ₗ[K] K}
  {b : Basis ι K V}
  {v : ι → V}
-- given
  (hB : B.Nondegenerate)
  (hv : ∀ i j, B (v i) (b j) = if j = i then 1 else 0) :
-- imply
  v = BilinForm.dualBasis B hB b :=
-- proof
  ((BilinForm.dualBasis_eq_iff hB b v).mpr hv).symm

/--
[cor_5_14_dual_lattice_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma cor_5_14_dual_lattice_free
  {B : V →ₗ[K] V →ₗ[K] K}
  {b : Basis ι K V}
-- given
  (hB : B.Nondegenerate) :
-- imply
  BilinForm.dualSubmodule B (span A (Set.range b)) = span A (Set.range (BilinForm.dualBasis B hB b)) :=
-- proof
  BilinForm.dualSubmodule_span_of_basis B hB b
end FreeDualLattice
section LocalizationDualLattice

/--
[Submodule.le_localize](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma Submodule.le_localize
  [CommRing A]
  [AddCommGroup V]
  [Module A V]
  {S : Submonoid A}
  {M : Submodule A V} :
-- imply
  M ≤ M.localize S :=
-- proof
  fun _ hv => ⟨1, S.one_mem, by simpa⟩

/--
[isLocALattice_of_localize](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma isLocALattice_of_localize
  [CommRing A]
  [IsDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [AddCommGroup V]
  [Module K V]
  [Module A V]
  [IsScalarTower A K V]
  {S : Submonoid A}
  {M : Submodule A V}
-- given
  (hM : IsALattice A K V M) :
-- imply
  IsLocALattice A K V S (M.localize S) := by
-- proof
  obtain ⟨⟨T, hT⟩, hspan⟩ := hM
  exact ⟨⟨T, by rw [hT]⟩, by
    rw [eq_top_iff]; rw [eq_top_iff] at hspan
    exact le_trans hspan (Submodule.span_mono (Submodule.le_localize S M))⟩

/--
[lem_5_15_localization_dual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma lem_5_15_localization_dual
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [AddCommGroup V]
  [Module K V]
  [Module A V]
  [IsScalarTower A K V]
  [FiniteDimensional K V]
  {B : V →ₗ[K] V →ₗ[K] K}
  {M : Submodule A V}
  {S : Submonoid A}
-- given
  (hB : B.Nondegenerate)
  (hM : IsALattice A K V M) :
-- imply
  IsLocALattice A K V S (M.localize S) ∧ IsLocALattice A K V S ((BilinForm.dualSubmodule B M).localize S) ∧ BilinForm.dualSubmoduleLoc B S (M.localize S) = (BilinForm.dualSubmodule B M).localize S := by
-- proof
  refine ⟨isLocALattice_of_localize S M hM,
    isLocALattice_of_localize S _ (dualSubmodule_isALattice B hB M hM), ?_⟩
  ext v
  constructor
  ·
    intro hv
    obtain ⟨⟨T, hT⟩, _⟩ := hM
    have hT_in_loc : ∀ m ∈ (T : Set V), m ∈ M.localize S :=
      fun m hm => Submodule.le_localize S M (hT ▸ Submodule.subset_span hm)
    have : ∀ m ∈ T, ∃ s ∈ S, s • (B v m) ∈ (1 : Submodule A K) :=
      fun m hm => hv m (hT_in_loc m hm)
    classical
    let s_fun : V → A := fun m => if hm : m ∈ T then (this m hm).choose else 1
    have hs_fun_mem : ∀ m ∈ T, s_fun m ∈ S := by
      intro m hm; simp only [s_fun, dif_pos hm]; exact (this m hm).choose_spec.1
    have hs_fun_prop : ∀ m ∈ T, s_fun m • (B v m) ∈ (1 : Submodule A K) := by
      intro m hm; simp only [s_fun, dif_pos hm]; exact (this m hm).choose_spec.2
    let s_prod := T.prod s_fun
    have hs_prod : s_prod ∈ S := Submonoid.prod_mem S hs_fun_mem
    refine ⟨s_prod, hs_prod, ?_⟩
    intro y hy
    rw [← hT] at hy
    have h_gen : ∀ m ∈ T, s_prod • ((B v) m) ∈ (1 : Submodule A K) := by
      intro m hm
      have hsplit : s_prod = (T.erase m).prod s_fun * s_fun m := by
        simp only [s_prod]; rw [← Finset.prod_erase_mul T s_fun hm]
      rw [hsplit, mul_smul]
      exact Submodule.smul_mem _ _ (hs_fun_prop m hm)
    have : y ∈ Submodule.comap ((B (s_prod • v)).restrictScalars A) (1 : Submodule A K) := by
      apply Submodule.span_le.mpr _ hy
      intro m hm
      show (B (s_prod • v)) m ∈ (1 : Submodule A K)
      have h1 : (B (s_prod • v)) m = s_prod • ((B v) m) := by
        conv_lhs =>
          rw [show s_prod • v = algebraMap A K s_prod • v from (algebraMap_smul K s_prod v).symm]
        simp [LinearMap.smul_apply, Algebra.smul_def]
      rw [h1]; exact h_gen m hm
    exact this
  ·
    intro ⟨s, hs, hsv⟩
    intro y ⟨t, ht, hty⟩
    have h1 : (B (s • v)) (t • y) ∈ (1 : Submodule A K) := hsv (t • y) hty
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    convert h1 using 1
    simp only [Algebra.smul_def, map_smul_of_tower, LinearMap.smul_apply, map_mul]
    ring
end LocalizationDualLattice
section DoubleDual
variable
  {A : Type*} [CommRing A]
  {K : Type*} [Field K] [Algebra A K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {ι : Type*} [Finite ι]

/--
[prop_5_16_double_dual_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma prop_5_16_double_dual_free
  {B : V →ₗ[K] V →ₗ[K] K}
  {b : Basis ι K V}
-- given
  (hB : B.Nondegenerate)
  (hB' : BilinForm.IsSymm B) :
-- imply
  BilinForm.dualSubmodule B (BilinForm.dualSubmodule B (span A (Set.range b))) = span A (Set.range b) :=
-- proof
  BilinForm.dualSubmodule_dualSubmodule_of_basis B hB hB' b

/--
[prop_2_6_lattice_eq_inter_localizations](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma prop_2_6_lattice_eq_inter_localizations
  [CommRing A]
  [AddCommGroup V]
  [Module A V]
  {M : Submodule A V}
  {v : V} :
-- imply
  (∀ P : MaximalSpectrum A, ∃ s ∈ P.asIdeal.primeCompl, s • v ∈ M) → v ∈ M := by
-- proof
  intro h
  let I : Ideal A :=
    { carrier := {a | a • v ∈ M}
      add_mem' := fun {a b} (ha : a • v ∈ M) (hb : b • v ∈ M) => by
        show (a + b) • v ∈ M; rw [add_smul]; exact M.add_mem ha hb
      zero_mem' := by show (0 : A) • v ∈ M; rw [zero_smul]; exact M.zero_mem
      smul_mem' := fun c {a} (ha : a • v ∈ M) => by
        show (c * a) • v ∈ M; rw [mul_smul]; exact M.smul_mem c ha }
  suffices hI : I = ⊤ by
    have h1 : (1 : A) ∈ I := hI ▸ Submodule.mem_top
    have h2 : (1 : A) • v ∈ M := h1
    rwa [one_smul] at h2
  by_contra hI
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨s, hs, hsv⟩ := h ⟨P, hP⟩
  exact hs (hIP hsv)

/--
[dvr_localize_lattice_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma dvr_localize_lattice_free
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [AddCommGroup V]
  [Module K V]
  [Module A V]
  [IsScalarTower A K V]
  [FiniteDimensional K V]
  {M : Submodule A V}
  {P : MaximalSpectrum A}
-- given
  (hM : IsALattice A K V M) :
-- imply
  ∃ (ι : Type) (_ : Fintype ι) (b : Basis ι K V), M.localize P.asIdeal.primeCompl = (Submodule.span A (Set.range b)).localize P.asIdeal.primeCompl := by
-- proof
  set S := P.asIdeal.primeCompl
  set AP := Localization.AtPrime P.asIdeal with AP_def
  haveI hfin : Module.Finite A ↥M := by rw [Module.Finite.iff_fg]; exact hM.fg
  haveI htf : Module.IsTorsionFree A ↥M := by
    constructor; intro a ha x y hxy; ext
    have h1 : (a : A) • (x : V) = a • (y : V) := congrArg Subtype.val hxy
    have ha' : algebraMap A K a ≠ 0 := by
      intro h; exact ha.ne_zero (IsFractionRing.injective A K (by simp [h]))
    rw [← IsScalarTower.algebraMap_smul K a (x : V),
      ← IsScalarTower.algebraMap_smul K a (y : V)] at h1
    exact smul_right_injective V ha' h1
  obtain ⟨n, bLM⟩ := @Module.basisOfFiniteTypeTorsionFree'
    (Localization.AtPrime P.asIdeal) _ (LocalizedModule S ↥M) _ _ _ _ _ _
  have hS_units : ∀ (s : S), IsUnit ((algebraMap A (Module.End A V)) (s : A)) := by
    intro ⟨s, hs⟩
    rw [Module.algebraMap_end_eq_smul_id]
    have hs' : algebraMap A K s ≠ 0 := by
      intro h
      exact nonZeroDivisors.ne_zero (Ideal.primeCompl_le_nonZeroDivisors P.asIdeal hs)
        (IsFractionRing.injective A K (by simp [h]))
    let inv : V →ₗ[A] V := {
      toFun := fun v => (algebraMap A K s)⁻¹ • v
      map_add' := by intros; simp [smul_add]
      map_smul' := by
        intros a v; simp only [RingHom.id_apply]
        rw [← IsScalarTower.algebraMap_smul K a v, smul_comm,
          IsScalarTower.algebraMap_smul K a]
    }
    refine ⟨⟨s • LinearMap.id, inv, ?_, ?_⟩, rfl⟩
    · ext v; show s • (inv v) = v
      simp only [inv, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← IsScalarTower.algebraMap_smul K s ((algebraMap A K s)⁻¹ • v)]
      simp [smul_smul, mul_inv_cancel₀ hs']
    · ext v; show inv (s • v) = v
      simp only [inv, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← IsScalarTower.algebraMap_smul K s v, smul_smul, inv_mul_cancel₀ hs', one_smul]
  let φ := LocalizedModule.lift S M.subtype hS_units
  have hφ_inj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using LocalizedModule.induction_on with
    | h m s =>
      rw [LocalizedModule.lift_mk] at hx
      set u := (hS_units s).unit
      have h1 : M.subtype m = 0 := by
        have key := congr_arg u.val hx
        simp only [map_zero] at key
        change (u.val ∘ₗ ↑u⁻¹) (M.subtype m) = 0 at key
        have : (u.val ∘ₗ ↑u⁻¹) = LinearMap.id := by
          ext v; show (u.val * u.inv) v = v; simp
        rw [this, LinearMap.id_apply] at key; exact key
      rw [show m = 0 from Subtype.ext h1, LocalizedModule.zero_mk]
  let e : Fin n → V := fun i => φ (bLM i)
  have hli : LinearIndependent K e := by
    rw [← LinearIndependent.iff_fractionRing (R := A) (K := K)]
    have hA_indep : LinearIndependent A (bLM : Fin n → LocalizedModule S ↥M) := by
      apply LinearIndependent.restrict_scalars (K := AP)
      · intro a b h
        exact IsLocalization.injective AP P.asIdeal.primeCompl_le_nonZeroDivisors (by simpa using h)
      · exact bLM.linearIndependent
    exact hA_indep.map' φ (LinearMap.ker_eq_bot.mpr hφ_inj)
  have hspan : Submodule.span K (Set.range e) = ⊤ := by
    rw [eq_top_iff, ← hM.span_eq_top]
    apply Submodule.span_le.mpr
    intro v hv
    set x : LocalizedModule S ↥M := LocalizedModule.mk ⟨v, hv⟩ 1
    have hφx : φ x = v := LocalizedModule.lift_mk_one S M.subtype hS_units ⟨v, hv⟩
    obtain ⟨⟨t, ht⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
      (M := S) (S := AP) (fun i : Fin n => bLM.repr x i)
    have hint' : ∀ i, ∃ a : A, algebraMap A AP a = (t : A) • bLM.repr x i := by
      intro i; exact hint i
    choose a_coeff ha_coeff using hint'
    have ht_ne : algebraMap A K t ≠ 0 := by
      intro hc
      have h0 : t = 0 := IsFractionRing.injective A K (by simp [hc])
      exact ht (h0 ▸ P.asIdeal.zero_mem)
    suffices h_tv : t • v ∈ Submodule.span A (Set.range e) by
      have h_tv_K := Submodule.span_le_restrictScalars A K _ h_tv
      rw [show v = (algebraMap A K t)⁻¹ • (algebraMap A K t • v) from by
        rw [smul_smul, inv_mul_cancel₀ ht_ne, one_smul]]
      rw [← IsScalarTower.algebraMap_smul K t v] at h_tv_K
      exact (Submodule.span K (Set.range e)).smul_mem _ h_tv_K
    have h1 : t • v = φ (t • x) := by rw [map_smul, hφx]
    have h2 : t • x = ∑ i, algebraMap A AP (a_coeff i) • bLM i := by
      conv_lhs => rw [← bLM.sum_repr x]
      rw [Finset.smul_sum]
      congr 1; ext i
      rw [show t • (bLM.repr x) i • bLM i = (t • (bLM.repr x) i) • bLM i from
        (smul_assoc t ((bLM.repr x) i) (bLM i)).symm]
      rw [← ha_coeff i, algebraMap_smul]
    rw [h1, h2, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [algebraMap_smul, map_smul]
    exact Submodule.smul_mem _ (a_coeff i) (Submodule.subset_span ⟨i, rfl⟩)
  let b := Basis.mk hli hspan.ge
  have h_M_to_span : ∀ w ∈ M, ∃ t ∈ S, t • w ∈ Submodule.span A (Set.range e) := by
    intro w hw
    set xw := LocalizedModule.mk (⟨w, hw⟩ : ↥M) (1 : S)
    have hφw : φ xw = w := LocalizedModule.lift_mk_one S M.subtype hS_units ⟨w, hw⟩
    obtain ⟨⟨tw, htw⟩, hintw⟩ := IsLocalization.exist_integer_multiples_of_finite
      (M := S) (S := AP) (fun i : Fin n => bLM.repr xw i)
    have hintw' : ∀ i, ∃ a : A, algebraMap A AP a = (tw : A) • bLM.repr xw i := by
      intro i; exact hintw i
    choose aw haw using hintw'
    refine ⟨tw, htw, ?_⟩
    rw [show tw • w = φ (tw • xw) by rw [map_smul, hφw]]
    have : tw • xw = ∑ i, algebraMap A AP (aw i) • bLM i := by
      conv_lhs => rw [← bLM.sum_repr xw]
      rw [Finset.smul_sum]; congr 1; ext i
      rw [show tw • (bLM.repr xw) i • bLM i = (tw • (bLM.repr xw) i) • bLM i from
        (smul_assoc tw ((bLM.repr xw) i) (bLM i)).symm]
      rw [← haw i, algebraMap_smul]
    rw [this, map_sum]
    apply Submodule.sum_mem; intro i _
    rw [algebraMap_smul, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h_e_to_M : ∀ i : Fin n, ∃ u ∈ S, u • e i ∈ M := by
    intro i
    induction hbi : bLM i using LocalizedModule.induction_on with
    | h mi si =>
      refine ⟨si, si.prop, ?_⟩
      show (si : A) • φ (bLM i) ∈ M
      rw [hbi]
      rw [← map_smul φ (si : A) (LocalizedModule.mk mi si)]
      rw [LocalizedModule.smul'_mk]
      have : LocalizedModule.mk ((si : A) • mi) si = LocalizedModule.mk mi (1 : S) :=
        LocalizedModule.mk_cancel si mi
      rw [this]
      rwa [LocalizedModule.lift_mk_one]
  refine ⟨Fin n, inferInstance, b, ?_⟩
  ext v
  simp only [Submodule.localize, Submodule.mem_mk]
  constructor
  ·
    rintro ⟨s, hs, hsv⟩
    obtain ⟨t, ht_mem, ht_span⟩ := h_M_to_span (s • v) hsv
    refine ⟨t * s, S.mul_mem ht_mem hs, ?_⟩
    rw [mul_smul]
    convert ht_span using 2
    simp only [b, Basis.coe_mk]
  ·
    rintro ⟨s, hs, hsv⟩
    have hsv' : s • v ∈ Submodule.span A (Set.range e) := by
      convert hsv using 2; simp only [b, Basis.coe_mk]
    choose u_fn hu_fn_mem hu_fn_in_M using h_e_to_M
    set u : A := ∏ i : Fin n, u_fn i
    have hu_mem : u ∈ S := Submonoid.prod_mem S (fun i _ => hu_fn_mem i)
    have hu_ei : ∀ i : Fin n, u • e i ∈ M := by
      intro i
      have : u = (∏ j ∈ (Finset.univ.erase i), u_fn j) * u_fn i := by
        rw [mul_comm]; exact (Finset.mul_prod_erase Finset.univ u_fn (Finset.mem_univ i)).symm
      rw [this, mul_smul]
      exact M.smul_mem _ (hu_fn_in_M i)
    refine ⟨u * s, S.mul_mem hu_mem hs, ?_⟩
    rw [mul_smul]
    apply Submodule.span_induction (p := fun x _ => u • x ∈ M) _ _ _ _ hsv'
    · rintro w ⟨i, rfl⟩; exact hu_ei i
    · simp [M.zero_mem]
    · intro x y _ _ hx hy; rw [smul_add]; exact M.add_mem hx hy
    · intro a x _ hx; rw [smul_comm]; exact M.smul_mem a hx

/--
[double_dual_local_dvr_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma double_dual_local_dvr_step
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [AddCommGroup V]
  [Module K V]
  [Module A V]
  [IsScalarTower A K V]
  [FiniteDimensional K V]
  {B : V →ₗ[K] V →ₗ[K] K}
  {M : Submodule A V}
  {P : MaximalSpectrum A}
  {v : V}
-- given
  (hB : B.Nondegenerate)
  (hB' : BilinForm.IsSymm B)
  (hM : IsALattice A K V M)
  (hv : v ∈ BilinForm.dualSubmodule B (BilinForm.dualSubmodule B M)) :
-- imply
  ∃ s ∈ P.asIdeal.primeCompl, s • v ∈ M := by
-- proof
  set S := P.asIdeal.primeCompl
  obtain ⟨ι, hfin, b, hMloc⟩ := dvr_localize_lattice_free M hM P
  set L := Submodule.span A (Set.range b) with hL_def
  have hL : IsALattice A K V L := by
    constructor
    · haveI : Finite ι := Finite.of_fintype ι
      exact Submodule.fg_span (Set.finite_range b)
    · rw [Submodule.span_span_of_tower]; exact b.span_eq
  have hLstar : IsALattice A K V (BilinForm.dualSubmodule B L) :=
    dualSubmodule_isALattice B hB L hL
  have hMstar : IsALattice A K V (BilinForm.dualSubmodule B M) :=
    dualSubmodule_isALattice B hB M hM
  have h515_M := (lem_5_15_localization_dual B hB M hM S).2.2
  have h515_Mstar := (lem_5_15_localization_dual B hB _ hMstar S).2.2
  have h515_L := (lem_5_15_localization_dual B hB L hL S).2.2
  have h515_Lstar := (lem_5_15_localization_dual B hB _ hLstar S).2.2
  have hfree : BilinForm.dualSubmodule B (BilinForm.dualSubmodule B L) = L := by
    haveI : Finite ι := Finite.of_fintype ι
    exact prop_5_16_double_dual_free B hB hB' b
  have hstar_eq : (BilinForm.dualSubmodule B M).localize S =
    (BilinForm.dualSubmodule B L).localize S := by
    rw [← h515_M, ← h515_L, hMloc]
  have hstarstar_eq : (BilinForm.dualSubmodule B (BilinForm.dualSubmodule B M)).localize S =
    (BilinForm.dualSubmodule B (BilinForm.dualSubmodule B L)).localize S := by
    rw [← h515_Mstar, ← h515_Lstar, hstar_eq]
  have hdd_eq : (BilinForm.dualSubmodule B (BilinForm.dualSubmodule B M)).localize S =
    M.localize S := by
    rw [hstarstar_eq, hfree, ← hMloc]
  have hv_loc : v ∈ (BilinForm.dualSubmodule B (BilinForm.dualSubmodule B M)).localize S :=
    Submodule.le_localize S _ hv
  rwa [hdd_eq] at hv_loc

/--
[double_dual_sub_original](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma double_dual_sub_original
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [AddCommGroup V]
  [Module K V]
  [Module A V]
  [IsScalarTower A K V]
  [FiniteDimensional K V]
  {B : V →ₗ[K] V →ₗ[K] K}
  {M : Submodule A V}
-- given
  (hB : B.Nondegenerate)
  (hB' : BilinForm.IsSymm B)
  (hM : IsALattice A K V M) :
-- imply
  BilinForm.dualSubmodule B (BilinForm.dualSubmodule B M) ≤ M := by
-- proof
  intro v hv
  exact prop_2_6_lattice_eq_inter_localizations M v fun P =>
    double_dual_local_dvr_step B hB hB' M hM P v hv

/--
[prop_5_16_double_dual_dedekind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
lemma prop_5_16_double_dual_dedekind
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [AddCommGroup V]
  [Module K V]
  [Module A V]
  [IsScalarTower A K V]
  [FiniteDimensional K V]
  {B : V →ₗ[K] V →ₗ[K] K}
  {M : Submodule A V}
-- given
  (hB : B.Nondegenerate)
  (hB' : BilinForm.IsSymm B)
  (hM : IsALattice A K V M) :
-- imply
  dualLattice A K V B (dualLattice A K V B M) = M := by
-- proof
  rw [dualLattice_eq_dualSubmodule, dualLattice_eq_dualSubmodule]
  apply le_antisymm
  ·
    exact double_dual_sub_original B hB hB' M hM
  ·
    intro v hv w hw
    have h1 := hw v hv
    rw [Submodule.mem_one] at h1 ⊢
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, by rw [hB'.eq w v] at ha; exact ha⟩
end DoubleDual
alias dualBasis_exists := prop_5_7_existence
alias dualBasis_unique := prop_5_7_uniqueness
alias dualSubmoduleToDual_injective := thm_5_12_injective
alias directSumBilinForm_nondegenerate := cor_5_13_directSumBilinForm_nondegenerate
alias localization_dual_comm := lem_5_15_localization_dual

/--
[dualSubmodule_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
private lemma dualSubmodule_antitone_eq
  {B : V →ₗ[K] V →ₗ[K] K} :
-- imply
  Antitone (BilinForm.dualSubmodule B : Submodule A V → Submodule A V) := by
-- proof
  apply dualSubmodule_antitone B

/--
[thm_5_12_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
private lemma thm_5_12_injective_eq
  [DecidableEq ι]
  [Finite ι]
  {B : V →ₗ[K] V →ₗ[K] K}
  {N : Submodule A V}
-- given
  (hB : B.Nondegenerate)
  (hN : span K (N : Set V) = ⊤) :
-- imply
  Function.Injective (BilinForm.dualSubmoduleToDual B N) := by
-- proof
  apply thm_5_12_injective B hB N hN

/--
[dualSubmodule_isALattice](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
private lemma dualSubmodule_isALattice_eq
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [AddCommGroup V]
  [Module K V]
  [Module A V]
  [IsScalarTower A K V]
  [FiniteDimensional K V]
  {B : V →ₗ[K] V →ₗ[K] K}
  {M : Submodule A V}
-- given
  (hB : B.Nondegenerate)
  (hM : IsALattice A K V M) :
-- imply
  IsALattice A K V (BilinForm.dualSubmodule B M) := by
-- proof
  apply dualSubmodule_isALattice B hB M hM

/--
[thm_5_12_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
private lemma thm_5_12_surjective_eq
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [AddCommGroup V]
  [Module K V]
  [Module A V]
  [IsScalarTower A K V]
  [FiniteDimensional K V]
  {B : V →ₗ[K] V →ₗ[K] K}
  {M : Submodule A V}
-- given
  (hB : B.Nondegenerate)
  (hM : IsALattice A K V M) :
-- imply
  Function.Surjective (BilinForm.dualSubmoduleToDual B M) := by
-- proof
  apply thm_5_12_surjective B hB M hM

/--
[thm_5_12](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean)
-/
@[path]
private lemma thm_5_12_eq
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [AddCommGroup V]
  [Module K V]
  [Module A V]
  [IsScalarTower A K V]
  [FiniteDimensional K V]
  {B : V →ₗ[K] V →ₗ[K] K}
  {M : Submodule A V}
-- given
  (hB : B.Nondegenerate)
  (hM : IsALattice A K V M) :
-- imply
  IsALattice A K V (BilinForm.dualSubmodule B M) ∧ Function.Bijective (BilinForm.dualSubmoduleToDual B M) := by
-- proof
  apply thm_5_12 B hB M hM


-- created on 2026-10-23
