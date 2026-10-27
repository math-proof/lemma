import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.NumberField.LatticeDiscriminant
open scoped Matrix


/--
[discr_mem_latticeDiscriminant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
lemma discr_mem_latticeDiscriminant
  [CommRing A] [Field K] [Algebra A K]
  {L : Type u} [Field L] [Algebra K L] [Algebra A L] [FiniteDimensional K L] [hAKL : IsScalarTower A K L]
  {M : Submodule A L}
  {b : Fin (Module.finrank K L) → L}
-- given
  (hb : ∀ i, b i ∈ M) :
-- imply
  Algebra.discr K b ∈ latticeDiscriminant A K M :=
-- proof
  Submodule.subset_span ⟨b, hb, rfl⟩

/--
[latticeDiscriminant_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
lemma latticeDiscriminant_mono
  [CommRing A] [Field K] [Algebra A K]
  {L : Type u} [Field L] [Algebra K L] [Algebra A L] [FiniteDimensional K L] [hAKL : IsScalarTower A K L]
  {M N : Submodule A L}
-- given
  (h : M ≤ N) :
-- imply
  latticeDiscriminant A K M ≤ latticeDiscriminant A K N := by
-- proof
  apply Submodule.span_mono
  rintro d ⟨b, hb, rfl⟩
  exact ⟨b, fun i ↦ h (hb i), rfl⟩

/--
[latticeDiscriminant_le_span_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
lemma latticeDiscriminant_le_span_singleton
  [CommRing A] [Field K] [Algebra A K]
  {L : Type u} [Field L] [Algebra K L] [Algebra A L] [FiniteDimensional K L] [hAKL : IsScalarTower A K L]
  {bK : Module.Basis (Fin (Module.finrank K L)) K L}
  {M : Submodule A L}
-- given
  (hM : M ≤ Submodule.span A (Set.range (bK : Fin _ → L))) :
-- imply
  latticeDiscriminant A K M ≤
    Submodule.span A {Algebra.discr K (bK : Fin _ → L)} := by
-- proof
  apply Submodule.span_le.mpr
  rintro d ⟨x, hx, rfl⟩
  classical
  have hentries : ∀ i j, bK.toMatrix x i j ∈ (algebraMap A K).range := by
    intro i j
    simp only [Module.Basis.toMatrix_apply]
    have hxj := hM (hx j)
    rw [Submodule.mem_span_range_iff_exists_fun] at hxj
    obtain ⟨c, hc⟩ := hxj
    rw [show x j = ∑ k, algebraMap A K (c k) • bK k from by
      rw [← hc]
      congr 1
      ext k
      rw [Algebra.smul_def, Algebra.smul_def,
        IsScalarTower.algebraMap_apply A K L],
      Module.Basis.repr_sum_self]
    exact ⟨c i, rfl⟩
  let PA : Matrix _ _ A := Matrix.of (fun i j => (hentries i j).choose)
  have hPA : bK.toMatrix x = PA.map (algebraMap A K) := by
    ext i j
    simp only [Matrix.map_apply]
    exact (hentries i j).choose_spec.symm
  have hcob : Algebra.discr K x =
    (bK.toMatrix x).det ^ 2 * Algebra.discr K (bK : Fin _ → L) := by
    conv_lhs => rw [show x = (⇑bK) ᵥ* ((bK.toMatrix x).map (algebraMap K L))
      from (bK.toMatrix_map_vecMul x).symm]
    exact Algebra.discr_of_matrix_vecMul (⇑bK) (bK.toMatrix x)
  rw [hcob, hPA, show (PA.map (algebraMap A K)).det = algebraMap A K PA.det from
    (RingHom.map_det (algebraMap A K) PA).symm,
    show (algebraMap A K PA.det) ^ 2 = algebraMap A K (PA.det ^ 2) from
      (map_pow _ _ _).symm,
    ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/--
[latticeDiscriminant_isFractional](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
lemma latticeDiscriminant_isFractional
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type u} [Field L] [Algebra K L] [Algebra A L] [FiniteDimensional K L] [hAKL : IsScalarTower A K L]
  {M : Submodule A L}
  {bN : Module.Basis (Fin (Module.finrank K L)) K L}
-- given
  (hMN : M ≤ Submodule.span A (Set.range (bN : Fin _ → L))) :
-- imply
  IsFractional (nonZeroDivisors A) (latticeDiscriminant A K M) := by
-- proof
  have hle : latticeDiscriminant A K M ≤
    ((FractionalIdeal.spanSingleton (nonZeroDivisors A)
      (Algebra.discr K (bN : Fin _ → L))) : Submodule A K) := by
    rw [FractionalIdeal.coe_spanSingleton]
    exact latticeDiscriminant_le_span_singleton (A := A) (K := K) bN M hMN
  exact FractionalIdeal.isFractional_of_le hle

/--
[latticeDiscriminant_ne_bot_of_basis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
lemma latticeDiscriminant_ne_bot_of_basis
  [CommRing A] [Field K] [Algebra A K]
  {L : Type u} [Field L] [Algebra K L] [Algebra A L] [FiniteDimensional K L] [hAKL : IsScalarTower A K L] [Algebra.IsSeparable K L]
  {M : Submodule A L}
  {bK : Module.Basis (Fin (Module.finrank K L)) K L}
-- given
  (hKM : Set.range (bK : Fin _ → L) ⊆ M) :
-- imply
  latticeDiscriminant A K M ≠ ⊥ := by
-- proof
  have hmem : Algebra.discr K (bK : Fin _ → L) ∈
    latticeDiscriminant A K M :=
    discr_mem_latticeDiscriminant (A := A) (K := K)
      (fun i => hKM (Set.mem_range_self i))
  intro hbot
  rw [hbot] at hmem
  simp only [Submodule.mem_bot] at hmem
  exact Algebra.discr_not_zero_of_basis K bK hmem

/--
[latticeDiscriminant_isFractional_and_ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
lemma latticeDiscriminant_isFractional_and_ne_bot
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type u} [Field L] [Algebra K L] [Algebra A L] [FiniteDimensional K L] [hAKL : IsScalarTower A K L] [Algebra.IsSeparable K L]
  {M : Submodule A L}
  {bK bN : Module.Basis (Fin (Module.finrank K L)) K L}
-- given
  (hKM : Set.range (bK : Fin _ → L) ⊆ M)
  (hMN : M ≤ Submodule.span A (Set.range (bN : Fin _ → L))) :
-- imply
  IsFractional (nonZeroDivisors A) (latticeDiscriminant A K M) ∧
    latticeDiscriminant A K M ≠ ⊥ :=
-- proof
  ⟨latticeDiscriminant_isFractional A K M bN hMN,
    latticeDiscriminant_ne_bot_of_basis A K M bK hKM⟩

/--
[latticeDiscriminant_eq_span_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
lemma latticeDiscriminant_eq_span_singleton
  [CommRing A] [Field K] [Algebra A K]
  {L : Type u} [Field L] [Algebra K L] [Algebra A L] [FiniteDimensional K L] [hAKL : IsScalarTower A K L]
  {bK : Module.Basis (Fin (Module.finrank K L)) K L}
  {M : Submodule A L}
-- given
  (hM_le : M ≤ Submodule.span A (Set.range (bK : Fin _ → L)))
  (hM_ge : Set.range (bK : Fin _ → L) ⊆ M) :
-- imply
  latticeDiscriminant A K M =
    Submodule.span A {Algebra.discr K (bK : Fin _ → L)} := by
-- proof
  apply le_antisymm
  · exact latticeDiscriminant_le_span_singleton (A := A) (K := K) bK M hM_le
  · apply Submodule.span_le.mpr
    intro d hd
    rw [Set.mem_singleton_iff.mp hd]
    exact discr_mem_latticeDiscriminant (A := A) (K := K)
      fun i => hM_ge (Set.mem_range_self i)

/--
[latticeDiscriminant_eq_imp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
lemma latticeDiscriminant_eq_imp_eq
  [CommRing A] [Field K] [Algebra A K]
  {L : Type u} [Field L] [Algebra K L] [Algebra A L] [FiniteDimensional K L] [hAKL : IsScalarTower A K L] [Algebra.IsSeparable K L]
  {M M' : Submodule A L}
  {bK bK' : Module.Basis (Fin (Module.finrank K L)) K L}
-- given
  (hAK : Function.Injective (algebraMap A K))
  (hle : M' ≤ M)
  (hM_le : M ≤ Submodule.span A (Set.range (bK : Fin _ → L)))
  (hM_ge : Set.range (bK : Fin _ → L) ⊆ M)
  (hM'_le : M' ≤ Submodule.span A (Set.range (bK' : Fin _ → L)))
  (hM'_ge : Set.range (bK' : Fin _ → L) ⊆ M')
  (hD : latticeDiscriminant A K M' = latticeDiscriminant A K M) :
-- imply
  M' = M := by
-- proof
  classical
  have hbK'_in_span : ∀ i, bK' i ∈ Submodule.span A (Set.range (bK : Fin _ → L)) :=
    fun i => hM_le (hle (hM'_ge (Set.mem_range_self i)))
  have hentries : ∀ i j, bK.toMatrix (bK' : Fin _ → L) i j ∈
    (algebraMap A K).range := by
    intro i j
    simp only [Module.Basis.toMatrix_apply]
    have hxj := hbK'_in_span j
    rw [Submodule.mem_span_range_iff_exists_fun] at hxj
    obtain ⟨c, hc⟩ := hxj
    rw [show bK' j = ∑ k, algebraMap A K (c k) • bK k from by
      rw [← hc]
      congr 1
      ext k
      rw [Algebra.smul_def, Algebra.smul_def,
        IsScalarTower.algebraMap_apply A K L],
      Module.Basis.repr_sum_self]
    exact ⟨c i, rfl⟩
  set PA : Matrix _ _ A := Matrix.of (fun i j => (hentries i j).choose)
  have hPA : bK.toMatrix (bK' : Fin _ → L) = PA.map (algebraMap A K) := by
    ext i j
    simp only [Matrix.map_apply]
    exact (hentries i j).choose_spec.symm
  have hdiscr : Algebra.discr K (bK' : Fin _ → L) =
    (algebraMap A K PA.det) ^ 2 * Algebra.discr K (bK : Fin _ → L) := by
    conv_lhs => rw [show (bK' : Fin _ → L) = (bK : Fin _ → L) ᵥ*
      ((bK.toMatrix (bK' : Fin _ → L)).map (algebraMap K L))
      from (bK.toMatrix_map_vecMul (bK' : Fin _ → L)).symm]
    rw [hPA]
    rw [Algebra.discr_of_matrix_vecMul (bK : Fin _ → L) (PA.map (algebraMap A K))]
    congr 1
    congr 1
    exact (RingHom.map_det (algebraMap A K) PA).symm
  have hD_eq : latticeDiscriminant A K M =
    Submodule.span A {Algebra.discr K (bK : Fin _ → L)} :=
    latticeDiscriminant_eq_span_singleton (A := A) (K := K) bK M hM_le hM_ge
  have hD'_eq : latticeDiscriminant A K M' =
    Submodule.span A {Algebra.discr K (bK' : Fin _ → L)} :=
    latticeDiscriminant_eq_span_singleton (A := A) (K := K) bK' M' hM'_le hM'_ge
  have hbK_in : Algebra.discr K (bK : Fin _ → L) ∈
    Submodule.span A {Algebra.discr K (bK' : Fin _ → L)} := by
    rw [← hD'_eq, hD, hD_eq]
    exact Submodule.subset_span (Set.mem_singleton _)
  rw [Submodule.mem_span_singleton] at hbK_in
  obtain ⟨c, hc⟩ := hbK_in
  have hdiscr_ne : Algebra.discr K (bK : Fin _ → L) ≠ 0 :=
    Algebra.discr_not_zero_of_basis K bK
  have hunit_K : algebraMap A K c * (algebraMap A K PA.det) ^ 2 = 1 := by
    have h1 : Algebra.discr K (bK : Fin _ → L) = algebraMap A K c *
      ((algebraMap A K PA.det) ^ 2 * Algebra.discr K (bK : Fin _ → L)) := by
      rw [← hdiscr, ← hc, Algebra.smul_def]
    have h2 : algebraMap A K c * (algebraMap A K PA.det) ^ 2 *
      Algebra.discr K (bK : Fin _ → L) =
      1 * Algebra.discr K (bK : Fin _ → L) := by
      rw [mul_assoc, ← h1, one_mul]
    exact mul_right_cancel₀ hdiscr_ne h2
  have hunit_A : c * PA.det ^ 2 = 1 := by
    apply hAK
    rwa [map_mul, map_pow, map_one]
  have hdetPA_unit : IsUnit PA.det := by
    rw [isUnit_iff_exists_inv]
    refine ⟨c * PA.det, ?_⟩
    have : PA.det * (c * PA.det) = c * PA.det ^ 2 := by ring
    rw [this, hunit_A]
  have hbK_recover : ∀ i, bK i ∈ Submodule.span A (Set.range (bK' : Fin _ → L)) := by
    have hbK'_eq : (bK' : Fin _ → L) =
      (bK : Fin _ → L) ᵥ* (PA.map (algebraMap A L)) := by
      ext i
      have := bK.toMatrix_map_vecMul (bK' : Fin _ → L)
      rw [hPA] at this
      rw [show (PA.map (algebraMap A K)).map (algebraMap K L) =
        PA.map (algebraMap A L) from by
        ext i j
        simp only [Matrix.map_apply, ← IsScalarTower.algebraMap_apply A K L]] at this
      exact congr_fun this.symm i
    have hbK_eq : (bK : Fin _ → L) =
      (bK' : Fin _ → L) ᵥ* (PA⁻¹.map (algebraMap A L)) := by
      rw [hbK'_eq, Matrix.vecMul_vecMul]
      have : PA.map (algebraMap A L) * PA⁻¹.map (algebraMap A L) = 1 := by
        rw [show PA.map (algebraMap A L) = (algebraMap A L).mapMatrix PA from rfl,
          show PA⁻¹.map (algebraMap A L) = (algebraMap A L).mapMatrix PA⁻¹ from rfl,
          ← map_mul, Matrix.mul_nonsing_inv PA hdetPA_unit, map_one]
      rw [this, Matrix.vecMul_one]
    intro i
    rw [hbK_eq]
    change (bK' ⬝ᵥ fun j => (algebraMap A L) (PA⁻¹ j i)) ∈ _
    rw [dotProduct]
    apply Submodule.sum_mem
    intro j _
    rw [mul_comm (bK' j) _, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hM_le_M' : M ≤ M' := by
    intro x hx
    have hx_span := hM_le hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hx_span
    obtain ⟨c_x, hcx⟩ := hx_span
    rw [← hcx]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    have := hbK_recover j
    rw [Submodule.mem_span_range_iff_exists_fun] at this
    obtain ⟨c_bK, hcbK⟩ := this
    rw [← hcbK]
    apply Submodule.sum_mem
    intro k _
    exact Submodule.smul_mem _ _ (hM'_ge (Set.mem_range_self k))
  exact le_antisymm hle hM_le_M'

/--
[latticeDiscriminant_eq_imp_eq_of_isFractionRing](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
lemma latticeDiscriminant_eq_imp_eq_of_isFractionRing
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type u} [Field L] [Algebra K L] [Algebra A L] [FiniteDimensional K L] [hAKL : IsScalarTower A K L] [Algebra.IsSeparable K L]
  {M M' : Submodule A L}
  {bK bK' : Module.Basis (Fin (Module.finrank K L)) K L}
-- given
  (hle : M' ≤ M)
  (hM_le : M ≤ Submodule.span A (Set.range (bK : Fin _ → L)))
  (hM_ge : Set.range (bK : Fin _ → L) ⊆ M)
  (hM'_le : M' ≤ Submodule.span A (Set.range (bK' : Fin _ → L)))
  (hM'_ge : Set.range (bK' : Fin _ → L) ⊆ M')
  (hD : latticeDiscriminant A K M' = latticeDiscriminant A K M) :
-- imply
  M' = M :=
-- proof
  latticeDiscriminant_eq_imp_eq (A := A) (K := K)
    (IsFractionRing.injective A K) M M' hle bK hM_le hM_ge bK' hM'_le hM'_ge hD


-- created on 2026-10-20
-- updated on 2026-10-26
