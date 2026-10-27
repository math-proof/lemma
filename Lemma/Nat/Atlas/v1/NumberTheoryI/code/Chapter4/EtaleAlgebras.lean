import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial IntermediateField


/--
[isSeparable_iff_exists_monic_irreducible_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/EtaleAlgebras.lean)
-/
@[path]
lemma isSeparable_iff_exists_monic_irreducible_separable
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L] :
-- imply
  Algebra.IsSeparable K L ↔ ∃ f : K[X], f.Monic ∧ Irreducible f ∧ f.Separable ∧ Nonempty (L ≃ₐ[K] AdjoinRoot f) := by
-- proof
  constructor
  · intro h
    obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
    have hα_sep := Algebra.IsSeparable.isSeparable K α
    have hα_int := hα_sep.isIntegral
    exact ⟨minpoly K α, minpoly.monic hα_int, minpoly.irreducible hα_int, hα_sep,
      ⟨((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv).symm.trans
        (IntermediateField.adjoinRootEquivAdjoin K hα_int).symm⟩⟩
  · rintro ⟨f, hf_monic, hf_irr, hf_sep, ⟨e⟩⟩
    haveI : Fact (Irreducible f) := ⟨hf_irr⟩
    have hf_ne := hf_monic.ne_zero
    have hroot_sep : IsSeparable K (AdjoinRoot.root f) := by
      show (minpoly K (AdjoinRoot.root f)).Separable
      rwa [AdjoinRoot.minpoly_root hf_ne, hf_monic.leadingCoeff, inv_one, C_1, mul_one]
    have hgen : K⟮AdjoinRoot.root f⟯ = (⊤ : IntermediateField K (AdjoinRoot f)) := by
      rw [IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
        hroot_sep.isIntegral.isAlgebraic,
        ← AdjoinRoot.powerBasis_gen hf_ne]
      exact PowerBasis.adjoin_gen_eq_top (AdjoinRoot.powerBasis hf_ne)
    rw [← isSeparable_adjoin_simple_iff_isSeparable] at hroot_sep
    haveI : Algebra.IsSeparable K (AdjoinRoot f) :=
      Algebra.IsSeparable.of_algHom K (↥K⟮AdjoinRoot.root f⟯)
        (IntermediateField.topEquiv.symm.trans (IntermediateField.equivOfEq hgen).symm).toAlgHom
    exact Algebra.IsSeparable.of_algHom K (AdjoinRoot f) e.toAlgHom
section SeparableTowerProperties

/--
[finSepDegree_le_finrank_and_eq_iff_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/EtaleAlgebras.lean)
-/
@[path]
lemma finSepDegree_le_finrank_and_eq_iff_separable
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L] :
-- imply
  Field.finSepDegree K L ≤ Module.finrank K L ∧ (Field.finSepDegree K L = Module.finrank K L ↔ Algebra.IsSeparable K L) :=
-- proof
  ⟨Field.finSepDegree_le_finrank K L, Field.finSepDegree_eq_finrank_iff K L⟩

/--
[isSeparable_tower_iff_of_finiteDimensional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/EtaleAlgebras.lean)
-/
@[path]
lemma isSeparable_tower_iff_of_finiteDimensional
  [Field K]
  [Field L]
  [Algebra K L]
  [Field F]
  [Algebra K F]
  [Algebra F L]
  [IsScalarTower K F L]
  [FiniteDimensional K L]
  [FiniteDimensional K F]
  [FiniteDimensional F L] :
-- imply
  Algebra.IsSeparable K L ↔ (Algebra.IsSeparable K F ∧ Algebra.IsSeparable F L) := by
-- proof
  constructor
  · intro h
    exact ⟨Algebra.isSeparable_tower_bot_of_isSeparable K F L,
      Algebra.isSeparable_tower_top_of_isSeparable K F L⟩
  · rintro ⟨_, _⟩
    exact Algebra.IsSeparable.trans K F L

/--
[isSeparable_tower_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/EtaleAlgebras.lean)
-/
@[path]
lemma isSeparable_tower_iff
  [Field K]
  [Field L]
  [Algebra K L]
  [Field F]
  [Algebra K F]
  [Algebra F L]
  [IsScalarTower K F L] :
-- imply
  Algebra.IsSeparable K L ↔ (Algebra.IsSeparable K F ∧ Algebra.IsSeparable F L) := by
-- proof
  constructor
  · intro h
    exact ⟨Algebra.isSeparable_tower_bot_of_isSeparable K F L,
      Algebra.isSeparable_tower_top_of_isSeparable K F L⟩
  · rintro ⟨_, _⟩
    exact Algebra.IsSeparable.trans K F L

/--
[separableClosure_isSeparable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/EtaleAlgebras.lean)
-/
@[path]
lemma separableClosure_isSeparable
  [Field K]
  [Field L]
  [Algebra K L] :
-- imply
  Algebra.IsSeparable K (separableClosure K L) :=
-- proof
  separableClosure.isSeparable K L

/--
[mem_separableClosure_iff_isSeparable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/EtaleAlgebras.lean)
-/
@[path]
lemma mem_separableClosure_iff_isSeparable
  [Field K]
  [Field L]
  [Algebra K L]
  {x : L} :
-- imply
  x ∈ separableClosure K L ↔ IsSeparable K x :=
-- proof
  mem_separableClosure_iff
end SeparableTowerProperties


-- created on 2026-10-23
