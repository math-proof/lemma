import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.LatticeDiscriminant
open scoped Matrix


/--
[discr_mem_latticeDiscriminant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
private lemma discr_mem_latticeDiscriminant_eq
  [CommRing A] [Field K] [Algebra A K]
  {L : Type u} [Field L] [Algebra K L] [Algebra A L] [FiniteDimensional K L] [hAKL : IsScalarTower A K L]
  {M : Submodule A L}
  {b : Fin (Module.finrank K L) → L}
-- given
  (hb : ∀ i, b i ∈ M) :
-- imply
  Algebra.discr K b ∈ latticeDiscriminant A K M := by
-- proof
  apply discr_mem_latticeDiscriminant A K hb

/--
[latticeDiscriminant_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
private lemma latticeDiscriminant_mono_eq
  [CommRing A] [Field K] [Algebra A K]
  {L : Type u} [Field L] [Algebra K L] [Algebra A L] [FiniteDimensional K L] [hAKL : IsScalarTower A K L]
  {M N : Submodule A L}
-- given
  (h : M ≤ N) :
-- imply
  latticeDiscriminant A K M ≤ latticeDiscriminant A K N := by
-- proof
  apply latticeDiscriminant_mono A K h

/--
[latticeDiscriminant_le_span_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
private lemma latticeDiscriminant_le_span_singleton_eq
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
  apply latticeDiscriminant_le_span_singleton A K bK M hM

/--
[latticeDiscriminant_isFractional](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
private lemma latticeDiscriminant_isFractional_eq
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type u} [Field L] [Algebra K L] [Algebra A L] [FiniteDimensional K L] [hAKL : IsScalarTower A K L]
  {M : Submodule A L}
  {bN : Module.Basis (Fin (Module.finrank K L)) K L}
-- given
  (hMN : M ≤ Submodule.span A (Set.range (bN : Fin _ → L))) :
-- imply
  IsFractional (nonZeroDivisors A) (latticeDiscriminant A K M) := by
-- proof
  apply latticeDiscriminant_isFractional A K M bN hMN

/--
[latticeDiscriminant_ne_bot_of_basis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
private lemma latticeDiscriminant_ne_bot_of_basis_eq
  [CommRing A] [Field K] [Algebra A K]
  {L : Type u} [Field L] [Algebra K L] [Algebra A L] [FiniteDimensional K L] [hAKL : IsScalarTower A K L] [Algebra.IsSeparable K L]
  {M : Submodule A L}
  {bK : Module.Basis (Fin (Module.finrank K L)) K L}
-- given
  (hKM : Set.range (bK : Fin _ → L) ⊆ M) :
-- imply
  latticeDiscriminant A K M ≠ ⊥ := by
-- proof
  apply latticeDiscriminant_ne_bot_of_basis A K M bK hKM

/--
[latticeDiscriminant_isFractional_and_ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
private lemma latticeDiscriminant_isFractional_and_ne_bot_eq
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type u} [Field L] [Algebra K L] [Algebra A L] [FiniteDimensional K L] [hAKL : IsScalarTower A K L] [Algebra.IsSeparable K L]
  {M : Submodule A L}
  {bK bN : Module.Basis (Fin (Module.finrank K L)) K L}
-- given
  (hKM : Set.range (bK : Fin _ → L) ⊆ M)
  (hMN : M ≤ Submodule.span A (Set.range (bN : Fin _ → L))) :
-- imply
  IsFractional (nonZeroDivisors A) (latticeDiscriminant A K M) ∧
    latticeDiscriminant A K M ≠ ⊥ := by
-- proof
  apply latticeDiscriminant_isFractional_and_ne_bot A K M bK hKM bN hMN

/--
[latticeDiscriminant_eq_span_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
private lemma latticeDiscriminant_eq_span_singleton_eq
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
  apply latticeDiscriminant_eq_span_singleton A K bK M hM_le hM_ge

/--
[latticeDiscriminant_eq_imp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
private lemma latticeDiscriminant_eq_imp_eq_eq
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
  apply latticeDiscriminant_eq_imp_eq A K hAK M M' hle bK hM_le hM_ge bK' hM'_le hM'_ge hD

/--
[latticeDiscriminant_eq_imp_eq_of_isFractionRing](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/LatticeDiscriminant.lean)
-/
@[path]
private lemma latticeDiscriminant_eq_imp_eq_of_isFractionRing_eq
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
  M' = M := by
-- proof
  apply latticeDiscriminant_eq_imp_eq_of_isFractionRing A K M M' hle bK hM_le hM_ge bK' hM'_le hM'_ge hD


-- created on 2026-10-20
