/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/LatticeDiscriminant.lean -/


import Def.NumberTheory.NumberField.LatticeDiscriminant
import Lemma.Nat.NumberField.LatticeDiscriminant
universe u

variable (A K : Type*) {L : Type u} [CommRing A] [Field K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L]


example (M : Submodule A L) :
    latticeDiscriminant A K M = Submodule.span A (latticeDiscriminantSet A K M) :=
  rfl

example (M : Submodule A L) (b : Fin (Module.finrank K L) → L)
    (hb : ∀ i, b i ∈ M) : Algebra.discr K b ∈ latticeDiscriminant A K M :=
  discr_mem_latticeDiscriminant A K hb

example {M N : Submodule A L} (h : M ≤ N) :
    latticeDiscriminant A K M ≤ latticeDiscriminant A K N :=
  latticeDiscriminant_mono A K h

example (M : Submodule A L) (bN : Module.Basis (Fin (Module.finrank K L)) K L)
    (hMN : M ≤ Submodule.span A (Set.range (bN : Fin _ → L))) :
    latticeDiscriminant A K M ≤
      Submodule.span A {Algebra.discr K (bN : Fin _ → L)} :=
  latticeDiscriminant_le_span_singleton A K bN M hMN

example [IsFractionRing A K] (M : Submodule A L)
    (bN : Module.Basis (Fin (Module.finrank K L)) K L)
    (hMN : M ≤ Submodule.span A (Set.range (bN : Fin _ → L))) :
    IsFractional (nonZeroDivisors A) (latticeDiscriminant A K M) :=
  latticeDiscriminant_isFractional A K M bN hMN

example [Algebra.IsSeparable K L] (M : Submodule A L)
    (bK : Module.Basis (Fin (Module.finrank K L)) K L)
    (hKM : Set.range (bK : Fin _ → L) ⊆ M) :
    latticeDiscriminant A K M ≠ ⊥ :=
  latticeDiscriminant_ne_bot_of_basis A K M bK hKM

example [IsFractionRing A K] [Algebra.IsSeparable K L] (M : Submodule A L)
    (bK : Module.Basis (Fin (Module.finrank K L)) K L)
    (hKM : Set.range (bK : Fin _ → L) ⊆ M)
    (bN : Module.Basis (Fin (Module.finrank K L)) K L)
    (hMN : M ≤ Submodule.span A (Set.range (bN : Fin _ → L))) :
    IsFractional (nonZeroDivisors A) (latticeDiscriminant A K M) ∧
      latticeDiscriminant A K M ≠ ⊥ :=
  latticeDiscriminant_isFractional_and_ne_bot A K M bK hKM bN hMN

example (M : Submodule A L) (bK : Module.Basis (Fin (Module.finrank K L)) K L)
    (hM_le : M ≤ Submodule.span A (Set.range (bK : Fin _ → L)))
    (hM_ge : Set.range (bK : Fin _ → L) ⊆ M) :
    latticeDiscriminant A K M =
      Submodule.span A {Algebra.discr K (bK : Fin _ → L)} :=
  latticeDiscriminant_eq_span_singleton A K bK M hM_le hM_ge

example [Algebra.IsSeparable K L] (M M' : Submodule A L) (hle : M' ≤ M)
    (bK : Module.Basis (Fin (Module.finrank K L)) K L)
    (hM_le : M ≤ Submodule.span A (Set.range (bK : Fin _ → L)))
    (hM_ge : Set.range (bK : Fin _ → L) ⊆ M)
    (bK' : Module.Basis (Fin (Module.finrank K L)) K L)
    (hM'_le : M' ≤ Submodule.span A (Set.range (bK' : Fin _ → L)))
    (hM'_ge : Set.range (bK' : Fin _ → L) ⊆ M')
    (hAK : Function.Injective (algebraMap A K))
    (hD : latticeDiscriminant A K M' = latticeDiscriminant A K M) :
    M' = M :=
  latticeDiscriminant_eq_imp_eq A K hAK M M' hle bK hM_le hM_ge bK' hM'_le
    hM'_ge hD

example [IsFractionRing A K] [Algebra.IsSeparable K L] (M M' : Submodule A L)
    (hle : M' ≤ M) (bK : Module.Basis (Fin (Module.finrank K L)) K L)
    (hM_le : M ≤ Submodule.span A (Set.range (bK : Fin _ → L)))
    (hM_ge : Set.range (bK : Fin _ → L) ⊆ M)
    (bK' : Module.Basis (Fin (Module.finrank K L)) K L)
    (hM'_le : M' ≤ Submodule.span A (Set.range (bK' : Fin _ → L)))
    (hM'_ge : Set.range (bK' : Fin _ → L) ⊆ M')
    (hD : latticeDiscriminant A K M' = latticeDiscriminant A K M) :
    M' = M :=
  latticeDiscriminant_eq_imp_eq_of_isFractionRing A K M M' hle bK hM_le hM_ge
    bK' hM'_le hM'_ge hD

example :
    let b : Module.Basis (Fin (Module.finrank ℚ ℚ)) ℚ ℚ :=
      (Module.Basis.singleton (Fin 1) ℚ).reindex
        (finCongr (Module.finrank_self ℚ).symm)
    let M : Submodule ℤ ℚ := Submodule.span ℤ (Set.range (b : Fin _ → ℚ))
    latticeDiscriminant ℤ ℚ M = Submodule.span ℤ {(1 : ℚ)} ∧
      IsFractional (nonZeroDivisors ℤ) (latticeDiscriminant ℤ ℚ M) := by
  intro b M
  have hb : ∀ i, b i = 1 := by
    have heq : b = (Module.Basis.singleton (Fin 1) ℚ).reindex
      (finCongr (Module.finrank_self ℚ).symm) := rfl
    intro i
    rw [heq, Module.Basis.reindex_apply, Module.Basis.singleton_apply]
  have hU : ∀ i j : Fin (Module.finrank ℚ ℚ), i = j := fun i j =>
    (finCongr (Module.finrank_self ℚ).symm).symm.injective (Subsingleton.elim _ _)
  have hmat : Algebra.traceMatrix ℚ (b : Fin (Module.finrank ℚ ℚ) → ℚ) = 1 := by
    ext i j
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb i, hb j, mul_one,
      Algebra.trace_self_apply, hU i j]
    exact (Matrix.one_apply_eq j).symm
  have hdiscr : Algebra.discr ℚ (b : Fin (Module.finrank ℚ ℚ) → ℚ) = 1 := by
    rw [Algebra.discr_def, hmat, Matrix.det_one]
  have hle : latticeDiscriminant ℤ ℚ M ≤ Submodule.span ℤ {(1 : ℚ)} := by
    have h := latticeDiscriminant_le_span_singleton ℤ ℚ b M le_rfl
    rwa [hdiscr] at h
  have hge : Submodule.span ℤ {(1 : ℚ)} ≤ latticeDiscriminant ℤ ℚ M := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    rw [← hdiscr]
    exact discr_mem_latticeDiscriminant ℤ ℚ
      (fun i => Submodule.subset_span (Set.mem_range_self i))
  have heq : latticeDiscriminant ℤ ℚ M = Submodule.span ℤ {(1 : ℚ)} :=
    le_antisymm hle hge
  exact ⟨heq, by
    rw [heq]
    exact FractionalIdeal.isFractional_span_singleton (S := nonZeroDivisors ℤ) (1 : ℚ)⟩

-- The discriminant of the lattice generated by `2` over `ℤ` in `ℚ` is `4`.
-- We compute `Algebra.discr` explicitly from the trace matrix rather than invoking
-- `latticeDiscriminant_eq_span_singleton`, whose calculation this example tests.
example :
    let M : Submodule ℤ ℚ := Submodule.span ℤ {(2 : ℚ)}
    latticeDiscriminant ℤ ℚ M = Submodule.span ℤ {(4 : ℚ)} := by
  intro M
  let b₀ : Module.Basis (Fin (Module.finrank ℚ ℚ)) ℚ ℚ :=
    (Module.Basis.singleton (Fin 1) ℚ).reindex
      (finCongr (Module.finrank_self ℚ).symm)
  let u : ℚˣ := ⟨2, 2⁻¹, by norm_num, by norm_num⟩
  let b : Module.Basis (Fin (Module.finrank ℚ ℚ)) ℚ ℚ :=
    b₀.unitsSMul (fun _ => u)
  have hb₀ : ∀ i, b₀ i = 1 := by
    have heq : b₀ = (Module.Basis.singleton (Fin 1) ℚ).reindex
      (finCongr (Module.finrank_self ℚ).symm) := rfl
    intro i
    rw [heq, Module.Basis.reindex_apply, Module.Basis.singleton_apply]
  have hu : (u : ℚ) = 2 := rfl
  have hb : ∀ i, b i = 2 := by
    intro i
    have heq : b = b₀.unitsSMul (fun _ => u) := rfl
    rw [heq, Module.Basis.unitsSMul_apply, hb₀ i, Units.smul_def, hu, smul_eq_mul,
      mul_one]
  have hU : ∀ i j : Fin (Module.finrank ℚ ℚ), i = j := fun i j =>
    (finCongr (Module.finrank_self ℚ).symm).symm.injective (Subsingleton.elim _ _)
  have hne : Nonempty (Fin (Module.finrank ℚ ℚ)) :=
    ⟨finCongr (Module.finrank_self ℚ).symm 0⟩
  have hmat : Algebra.traceMatrix ℚ (b : Fin (Module.finrank ℚ ℚ) → ℚ) =
      (4 : ℚ) • (1 : Matrix _ _ ℚ) := by
    ext i j
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb i, hb j]
    have hij : i = j := hU i j
    subst hij
    rw [Matrix.smul_apply, Matrix.one_apply_eq]
    norm_num [Algebra.trace_self_apply]
  have hdiscr : Algebra.discr ℚ (b : Fin (Module.finrank ℚ ℚ) → ℚ) = 4 := by
    rw [Algebra.discr_def, hmat, Matrix.det_smul, Matrix.det_one,
      Fintype.card_fin, Module.finrank_self, pow_one, mul_one]
  have hrange : Set.range (b : Fin (Module.finrank ℚ ℚ) → ℚ) = {(2 : ℚ)} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      exact hb i
    · intro hx
      obtain ⟨i₀⟩ := hne
      exact ⟨i₀, by rw [hb i₀, hx]⟩
  have hM_le : M ≤ Submodule.span ℤ (Set.range (b : Fin _ → ℚ)) := by
    have hM : M = Submodule.span ℤ (Set.range (b : Fin _ → ℚ)) := by
      change Submodule.span ℤ {(2 : ℚ)} = _
      rw [hrange]
    rw [hM]
  have hM_ge : Set.range (b : Fin (Module.finrank ℚ ℚ) → ℚ) ⊆ M := by
    rw [hrange]
    exact Submodule.subset_span
  have hle : latticeDiscriminant ℤ ℚ M ≤ Submodule.span ℤ {(4 : ℚ)} := by
    have h := latticeDiscriminant_le_span_singleton ℤ ℚ b M hM_le
    rwa [hdiscr] at h
  have hge : Submodule.span ℤ {(4 : ℚ)} ≤ latticeDiscriminant ℤ ℚ M := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    rw [← hdiscr]
    exact discr_mem_latticeDiscriminant ℤ ℚ
      (fun i => Submodule.subset_span (Set.mem_singleton_iff.mpr (hb i)))
  exact le_antisymm hle hge

-- Rigidity on an actual equal-discriminant inclusion: the spans of `1` and `-1`
-- in `ℚ` have the same discriminant, so the rigidity theorem forces them equal.
example :
    let M : Submodule ℤ ℚ := Submodule.span ℤ {(1 : ℚ)}
    let M' : Submodule ℤ ℚ := Submodule.span ℤ {(-1 : ℚ)}
    M' = M := by
  intro M M'
  let b₀ : Module.Basis (Fin (Module.finrank ℚ ℚ)) ℚ ℚ :=
    (Module.Basis.singleton (Fin 1) ℚ).reindex
      (finCongr (Module.finrank_self ℚ).symm)
  have hb₀ : ∀ i, b₀ i = 1 := by
    have heq : b₀ = (Module.Basis.singleton (Fin 1) ℚ).reindex
      (finCongr (Module.finrank_self ℚ).symm) := rfl
    intro i
    rw [heq, Module.Basis.reindex_apply, Module.Basis.singleton_apply]
  have hU : ∀ i j : Fin (Module.finrank ℚ ℚ), i = j := fun i j =>
    (finCongr (Module.finrank_self ℚ).symm).symm.injective (Subsingleton.elim _ _)
  have hne : Nonempty (Fin (Module.finrank ℚ ℚ)) :=
    ⟨finCongr (Module.finrank_self ℚ).symm 0⟩
  -- The basis constantly `-1`.
  let u : ℚˣ := ⟨-1, -1, by norm_num, by norm_num⟩
  let b : Module.Basis (Fin (Module.finrank ℚ ℚ)) ℚ ℚ :=
    b₀.unitsSMul (fun _ => u)
  have hu : (u : ℚ) = -1 := rfl
  have hb : ∀ i, b i = -1 := by
    intro i
    have heq : b = b₀.unitsSMul (fun _ => u) := rfl
    rw [heq, Module.Basis.unitsSMul_apply, hb₀ i, Units.smul_def, hu, smul_eq_mul,
      mul_one]
  have hmat : Algebra.traceMatrix ℚ (b : Fin (Module.finrank ℚ ℚ) → ℚ) = 1 := by
    ext i j
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb i, hb j,
      neg_mul_neg, one_mul, Algebra.trace_self_apply, hU i j]
    exact (Matrix.one_apply_eq j).symm
  have hdiscr : Algebra.discr ℚ (b : Fin (Module.finrank ℚ ℚ) → ℚ) = 1 := by
    rw [Algebra.discr_def, hmat, Matrix.det_one]
  have hrange : Set.range (b : Fin (Module.finrank ℚ ℚ) → ℚ) = {(-1 : ℚ)} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      exact hb i
    · intro hx
      obtain ⟨i₀⟩ := hne
      exact ⟨i₀, by rw [hb i₀, hx]⟩
  have hrange₀ : Set.range (b₀ : Fin (Module.finrank ℚ ℚ) → ℚ) = {(1 : ℚ)} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      exact hb₀ i
    · intro hx
      obtain ⟨i₀⟩ := hne
      exact ⟨i₀, by rw [hb₀ i₀, hx]⟩
  have hM_le : M ≤ Submodule.span ℤ (Set.range (b₀ : Fin _ → ℚ)) := by
    have hM : M = Submodule.span ℤ (Set.range (b₀ : Fin _ → ℚ)) := by
      change Submodule.span ℤ {(1 : ℚ)} = _
      rw [hrange₀]
    rw [hM]
  have hM_ge : Set.range (b₀ : Fin (Module.finrank ℚ ℚ) → ℚ) ⊆ M := by
    have hM : M = Submodule.span ℤ (Set.range (b₀ : Fin _ → ℚ)) := by
      change Submodule.span ℤ {(1 : ℚ)} = _
      rw [hrange₀]
    rw [hM]
    exact Submodule.subset_span
  have hM'_le : M' ≤ Submodule.span ℤ (Set.range (b : Fin _ → ℚ)) := by
    have hM' : M' = Submodule.span ℤ (Set.range (b : Fin _ → ℚ)) := by
      change Submodule.span ℤ {(-1 : ℚ)} = _
      rw [hrange]
    rw [hM']
  have hM'_ge : Set.range (b : Fin (Module.finrank ℚ ℚ) → ℚ) ⊆ M' := by
    have hM' : M' = Submodule.span ℤ (Set.range (b : Fin _ → ℚ)) := by
      change Submodule.span ℤ {(-1 : ℚ)} = _
      rw [hrange]
    rw [hM']
    exact Submodule.subset_span
  have hle : M' ≤ M := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    change (-1 : ℚ) ∈ M
    have h1 : (1 : ℚ) ∈ M := Submodule.subset_span (Set.mem_singleton _)
    simpa using neg_mem h1
  have hD : latticeDiscriminant ℤ ℚ M' = latticeDiscriminant ℤ ℚ M := by
    have hmat₀ : Algebra.traceMatrix ℚ (b₀ : Fin (Module.finrank ℚ ℚ) → ℚ) =
        1 := by
      ext i j
      rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb₀ i, hb₀ j,
        mul_one, Algebra.trace_self_apply, hU i j]
      exact (Matrix.one_apply_eq j).symm
    have hdiscr₀ : Algebra.discr ℚ (b₀ : Fin (Module.finrank ℚ ℚ) → ℚ) = 1 := by
      rw [Algebra.discr_def, hmat₀, Matrix.det_one]
    have hDM : latticeDiscriminant ℤ ℚ M = Submodule.span ℤ {(1 : ℚ)} := by
      have h := latticeDiscriminant_eq_span_singleton ℤ ℚ b₀ M hM_le hM_ge
      rwa [hdiscr₀] at h
    have hDM' : latticeDiscriminant ℤ ℚ M' = Submodule.span ℤ {(1 : ℚ)} := by
      have h := latticeDiscriminant_eq_span_singleton ℤ ℚ b M' hM'_le hM'_ge
      rwa [hdiscr] at h
    rw [hDM', hDM]
  exact latticeDiscriminant_eq_imp_eq_of_isFractionRing ℤ ℚ M M' hle b₀ hM_le
    hM_ge b hM'_le hM'_ge hD

