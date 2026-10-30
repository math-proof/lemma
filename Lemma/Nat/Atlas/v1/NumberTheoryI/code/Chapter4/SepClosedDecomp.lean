import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.Chapter4.SepClosedDecomp.Part2
open Polynomial TensorProduct Module SepClosedDecomposition


/--
[algHom_card_eq_finrank_of_isSepClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/SepClosedDecomp.lean)
-/
@[path]
private lemma algHom_card_eq_finrank_of_isSepClosed_eq
  [Field K]
  [Field L]
  [Field Ω]
  [Algebra K L]
  [Algebra K Ω]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [IsSepClosed Ω] :
-- imply
  Fintype.card (L →ₐ[K] Ω) = finrank K L := by
-- proof
  apply SepClosedDecomposition.algHom_card_eq_finrank_of_isSepClosed K L Ω

/--
[algHom_linearIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/SepClosedDecomp.lean)
-/
@[path]
private lemma algHom_linearIndependent_eq
  [Field K]
  [Field L]
  [Field Ω]
  [Algebra K L]
  [Algebra K Ω]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [IsSepClosed Ω] :
-- imply
  LinearIndependent Ω (fun (σ : L →ₐ[K] Ω) (l : L) => σ l) := by
-- proof
  apply SepClosedDecomposition.algHom_linearIndependent K L Ω

/--
[column_functions_linearIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/SepClosedDecomp.lean)
-/
@[path]
private lemma column_functions_linearIndependent_eq
  [Field K]
  [Field L]
  [Field Ω]
  [Algebra K L]
  [Algebra K Ω]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [IsSepClosed Ω] :
-- imply
  LinearIndependent Ω (fun (i : Fin (finrank K L)) (φ : L →ₐ[K] Ω) => φ (finBasis K L i)) := by
-- proof
  apply SepClosedDecomposition.column_functions_linearIndependent K L Ω

/--
[tensorSepClosedAlgHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/SepClosedDecomp.lean)
-/
@[path]
private lemma tensorSepClosedAlgHom_injective_eq
  [Field K]
  [Field L]
  [Field Ω]
  [Algebra K L]
  [Algebra K Ω]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [IsSepClosed Ω] :
-- imply
  Function.Injective (tensorSepClosedAlgHom K L Ω) := by
-- proof
  apply SepClosedDecomposition.tensorSepClosedAlgHom_injective K L Ω

/--
[finrank_tensor_eq_finrank_pi_of_isSepClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/SepClosedDecomp.lean)
-/
@[path]
private lemma finrank_tensor_eq_finrank_pi_of_isSepClosed_eq
  [Field K]
  [Field L]
  [Field Ω]
  [Algebra K L]
  [Algebra K Ω]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [IsSepClosed Ω] :
-- imply
  finrank Ω (Ω ⊗[K] L) = finrank Ω ((L →ₐ[K] Ω) → Ω) := by
-- proof
  apply SepClosedDecomposition.finrank_tensor_eq_finrank_pi_of_isSepClosed K L Ω

/--
[tensorSepClosedAlgHom_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/SepClosedDecomp.lean)
-/
@[path]
private lemma tensorSepClosedAlgHom_surjective_eq
  [Field K]
  [Field L]
  [Field Ω]
  [Algebra K L]
  [Algebra K Ω]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [IsSepClosed Ω] :
-- imply
  Function.Surjective (tensorSepClosedAlgHom K L Ω) := by
-- proof
  apply SepClosedDecomposition.tensorSepClosedAlgHom_surjective K L Ω

/--
[tensorSepClosedAlgHom_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/SepClosedDecomp.lean)
-/
@[path]
private lemma tensorSepClosedAlgHom_bijective_eq
  [Field K]
  [Field L]
  [Field Ω]
  [Algebra K L]
  [Algebra K Ω]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [IsSepClosed Ω] :
-- imply
  Function.Bijective (tensorSepClosedAlgHom K L Ω) := by
-- proof
  apply SepClosedDecomposition.tensorSepClosedAlgHom_bijective K L Ω


-- created on 2026-10-23
-- updated on 2026-10-29
