import Mathlib
import sympy.Basic
import sympy.Algebra.Lie.LeviDecomposition

open LeviDecomposition

/--
[levi_sum_repr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma sum_repr
  [Semiring K] [AddCommMonoid V] [Module K V] [Fintype ι]
-- given
  (b : Module.Basis ι K V) (x : V) :
-- imply
  ∑ i, b.repr x i • b i = x := by
-- proof
  apply levi_sum_repr b x


/--
[levi_repr_eq_dual](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma repr_eq_dual
  [Field K] [AddCommGroup V] [Module K V] [Finite ι] [DecidableEq ι]
-- given
  (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
  (b : Module.Basis ι K V) (x : V) (i : ι) :
-- imply
  b.repr x i = B (B.dualBasis hB b i) x := by
-- proof
  apply levi_repr_eq_dual hB b x i


/--
[leviTraceKernel_isSolvable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma traceKernel_isSolvable
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Finite K M] [LieModule.IsFaithful K L M] :
-- imply
  LieAlgebra.IsSolvable (leviTraceKernel (K := K) (L := L) (M := M)) := by
-- proof
  apply leviTraceKernel_isSolvable


/--
[levi_traceForm_nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma nondegenerate_traceForm_levi
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [LieAlgebra.IsSemisimple K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] [Module.Finite K M]
  [LieModule.IsFaithful K L M] :
-- imply
  (LieModule.traceForm K L M).Nondegenerate := by
-- proof
  apply levi_traceForm_nondegenerate


/--
[levi_trace_casimir](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma trace_casimir
  [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Free K M] [Module.Finite K M]
-- given
  (hβ : (LieModule.traceForm K L M).Nondegenerate) :
-- imply
  LinearMap.trace K M (leviCasimir hβ) = (Module.finrank K L : K) := by
-- proof
  apply levi_trace_casimir hβ


/--
[levi_lie_dualBasis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma lie_dualBasis
  [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] [Fintype ι] [DecidableEq ι]
-- given
  (hβ : (LieModule.traceForm K L M).Nondegenerate)
  (b : Module.Basis ι K L) (x : L) (i : ι) :
-- imply
  Bracket.bracket x ((LieModule.traceForm K L M).dualBasis hβ b i) =
    -∑ j, b.repr (Bracket.bracket x (b j)) i •
      (LieModule.traceForm K L M).dualBasis hβ b j := by
-- proof
  apply levi_lie_dualBasis hβ b x i


/--
[levi_casimir_commute](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma casimir_commute
  [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Free K M] [Module.Finite K M]
-- given
  (hβ : (LieModule.traceForm K L M).Nondegenerate) (x : L) :
-- imply
  Commute (leviCasimir hβ) (LieModule.toEnd K L M x) := by
-- proof
  apply levi_casimir_commute hβ x


/--
[levi_casimir_range_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma casimir_range_le
  [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Free K M] [Module.Finite K M]
-- given
  (W : Submodule K M) (hβ : (LieModule.traceForm K L M).Nondegenerate)
  (hW : ∀ (x : L) (m : M), LieModule.toEnd K L M x m ∈ W) :
-- imply
  LinearMap.range (leviCasimir hβ) ≤ W := by
-- proof
  apply levi_casimir_range_le hβ W hW


/--
[levi_isKilling_killingCompl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma isKilling_killingCompl
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [LieAlgebra.IsSemisimple K L]
-- given
  (I : LieIdeal K L) :
-- imply
  LieAlgebra.IsKilling K I.killingCompl := by
-- proof
  apply levi_isKilling_killingCompl I


/--
[levi_isFaithful_killingCompl_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma isFaithful_killingCompl_ker
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [LieAlgebra.IsSemisimple K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] :
-- imply
  LieModule.IsFaithful K (LieModule.ker K L M).killingCompl M := by
-- proof
  apply levi_isFaithful_killingCompl_ker


/--
[levi_lie_top_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma lie_top_eq_top
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieAlgebra.IsSemisimple K L] :
-- imply
  Bracket.bracket (⊤ : LieIdeal K L) (⊤ : LieIdeal K L) = ⊤ := by
-- proof
  apply levi_lie_top_eq_top


/--
[levi_codim_one_action_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma codim_one_action_mem
  [Field K] [LieRing L] [LieAlgebra K L] [LieAlgebra.IsSemisimple K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Finite K M]
-- given
  (W : LieSubmodule K L M) (hW : Module.finrank K (M ⧸ W) = 1) :
-- imply
  ∀ (x : L) (m : M), Bracket.bracket x m ∈ W := by
-- proof
  apply levi_codim_one_action_mem W hW


/--
[levi_exists_isCompl_of_trivial_action](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma exists_isCompl_of_trivial_action
  [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (htriv : ∀ (x : L) (m : M), Bracket.bracket x m = 0) (W : LieSubmodule K L M) :
-- imply
  ∃ U : LieSubmodule K L M, IsCompl W U := by
-- proof
  apply levi_exists_isCompl_of_trivial_action htriv W


/--
[levi_finrank_quotient_comap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma finrank_quotient_comap
  [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] [Module.Finite K M]
-- given
  (V W : LieSubmodule K L M) (hVW : V ⊔ W = ⊤) :
-- imply
  Module.finrank K (V ⧸ W.comap V.incl) = Module.finrank K (M ⧸ W) := by
-- proof
  apply levi_finrank_quotient_comap V W hVW


/--
[levi_isCompl_map_of_isCompl_comap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma isCompl_map_of_isCompl_comap
  [CommRing K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (V W : LieSubmodule K L M) (U : LieSubmodule K L V) (hVW : V ⊔ W = ⊤)
  (hU : IsCompl (W.comap V.incl) U) :
-- imply
  IsCompl W (U.map V.incl) := by
-- proof
  apply levi_isCompl_map_of_isCompl_comap V W hVW U hU


/--
[levi_codim_one_complement](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma codim_one_complement
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [LieAlgebra.IsSemisimple K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] [Module.Finite K M]
-- given
  (W : LieSubmodule K L M) (hquot : Module.finrank K (M ⧸ W) = 1) :
-- imply
  ∃ U : LieSubmodule K L M, IsCompl W U := by
-- proof
  apply levi_codim_one_complement W hquot


/--
[levi_scalar_unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma scalar_unique
  [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (W : LieSubmodule K L M) (a b : K) (hW : W ≠ ⊥)
  (h : ∀ w : W, a • w = b • w) :
-- imply
  a = b := by
-- proof
  apply levi_scalar_unique W hW h


/--
[leviHomScalar_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma homScalar_apply
  [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (W : LieSubmodule K L M) (hW : W ≠ ⊥) (f : leviHomScalarMaps W) (w : W) :
-- imply
  f.1 w = leviHomScalar W hW f • w := by
-- proof
  apply leviHomScalar_apply W hW f w


/--
[leviHomScalar_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma homScalar_ker
  [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
-- imply
  LinearMap.ker (leviHomScalar W hW) =
    (leviHomVanishing W).toSubmodule.comap
      (leviHomScalarMaps W).toSubmodule.subtype := by
-- proof
  apply leviHomScalar_ker W hW


/--
[leviHomScalar_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma homScalar_surjective
  [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
-- imply
  Function.Surjective (leviHomScalar W hW) := by
-- proof
  apply leviHomScalar_surjective W hW


/--
[leviHomScalarMaps_quotient_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma homScalarMaps_quotient_finrank
  [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] [Module.Finite K M]
-- given
  (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
-- imply
  Module.finrank K
    (leviHomScalarMaps W ⧸
      (leviHomVanishing W).comap (leviHomScalarMaps W).incl) = 1 := by
-- proof
  apply leviHomScalarMaps_quotient_finrank W hW


/--
[levi_lie_mem_HomVanishing_of_mem_scalarMaps](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma lie_mem_HomVanishing_of_mem_scalarMaps
  [CommRing K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (W : LieSubmodule K L M) (f : leviHomScalarMaps W) (x : L) :
-- imply
  Bracket.bracket x (f.1 : M →ₗ[K] W) ∈ leviHomVanishing W := by
-- proof
  apply levi_lie_mem_HomVanishing_of_mem_scalarMaps W f x


/--
[leviFactorLieModule](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma factorLieModule
  [CommRing K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, Bracket.bracket x m = 0) :
-- imply
  @LieModule K (L ⧸ I) M _ _ _ _ _ (leviFactorLieRingModule I hI) := by
-- proof
  apply leviFactorLieModule I hI


/--
[leviFactorAction_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma factorAction_mk
  [CommRing K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, Bracket.bracket x m = 0) (x : L) (m : M) :
-- imply
  leviFactorAction I hI (LieSubmodule.Quotient.mk x) m = Bracket.bracket x m := by
-- proof
  apply leviFactorAction_mk I hI x m


/--
[levi_factor_exists_isCompl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma factor_exists_isCompl
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Finite K M]
-- given
  (I : LieIdeal K L) (hI_semisimple : LieAlgebra.IsSemisimple K (L ⧸ I))
  (hI : ∀ x ∈ I, ∀ m : M, Bracket.bracket x m = 0) (W : LieSubmodule K L M) :
-- imply
  ∃ U : LieSubmodule K L M, IsCompl W U := by
-- proof
  have := hI_semisimple
  apply levi_factor_exists_isCompl I hI W


/--
[leviQuotientMk_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma quotientMk_apply
  [CommRing K] [LieRing L] [LieAlgebra K L]
-- given
  (I : LieIdeal K L) (x : L) :
-- imply
  leviQuotientMk I x = LieSubmodule.Quotient.mk x := by
-- proof
  apply leviQuotientMk_apply I x


/--
[leviQuotientMk_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma quotientMk_surjective
  [CommRing K] [LieRing L] [LieAlgebra K L]
-- given
  (I : LieIdeal K L) :
-- imply
  Function.Surjective (leviQuotientMk I) := by
-- proof
  apply leviQuotientMk_surjective I


/--
[leviQuotientMk_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma quotientMk_ker
  [CommRing K] [LieRing L] [LieAlgebra K L]
-- given
  (I : LieIdeal K L) :
-- imply
  (leviQuotientMk I).ker = I := by
-- proof
  apply leviQuotientMk_ker I


/--
[levi_isSolvable_of_ker_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma isSolvable_of_ker_quotient
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L'] [LieAlgebra.IsSolvable L']
-- given
  (f : LieHom K L L') (hker : LieAlgebra.IsSolvable f.ker)
  (hf : Function.Surjective f) :
-- imply
  LieAlgebra.IsSolvable L := by
-- proof
  have := hker
  apply levi_isSolvable_of_ker_quotient f hf


/--
[leviComapMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma comapMap_surjective
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L']
-- given
  (f : LieHom K L L') (hf : Function.Surjective f) (J : LieIdeal K L') :
-- imply
  Function.Surjective (leviComapMap f J) := by
-- proof
  apply leviComapMap_surjective f hf J


/--
[leviComapMapKerToKer_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma comapMapKerToKer_injective
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L']
-- given
  (f : LieHom K L L') (J : LieIdeal K L') :
-- imply
  Function.Injective (leviComapMapKerToKer f J) := by
-- proof
  apply leviComapMapKerToKer_injective f J


/--
[levi_isSolvable_comap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma isSolvable_comap
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L']
-- given
  (f : LieHom K L L') (hker : LieAlgebra.IsSolvable f.ker) (hf : Function.Surjective f)
  (J : LieIdeal K L') [LieAlgebra.IsSolvable J] :
-- imply
  LieAlgebra.IsSolvable (J.comap f) := by
-- proof
  have := hker
  apply levi_isSolvable_comap f hf J


/--
[leviMapRestrict_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma mapRestrict_surjective
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L']
-- given
  (f : LieHom K L L') (hf : Function.Surjective f) (I : LieIdeal K L) :
-- imply
  Function.Surjective (leviMapRestrict f I) := by
-- proof
  apply leviMapRestrict_surjective f hf I


/--
[levi_isSolvable_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma isSolvable_map
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L']
-- given
  (f : LieHom K L L') (hf : Function.Surjective f) (I : LieIdeal K L)
  [LieAlgebra.IsSolvable I] :
-- imply
  LieAlgebra.IsSolvable (I.map f) := by
-- proof
  apply levi_isSolvable_map f hf I


/--
[levi_radical_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma radical_quotient
  [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
-- given
  (I : LieIdeal K L) (hI : I ≤ LieAlgebra.radical K L) :
-- imply
  (LieAlgebra.radical K L).map (leviQuotientMk I) =
    LieAlgebra.radical K (L ⧸ I) := by
-- proof
  apply levi_radical_quotient I hI


/--
[levi_radical_quotient_radical_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma radical_quotient_radical_eq_bot
  [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L] :
-- imply
  LieAlgebra.radical K (L ⧸ LieAlgebra.radical K L) = ⊥ := by
-- proof
  apply levi_radical_quotient_radical_eq_bot


/--
[levi_quotient_radical_isSemisimple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma quotient_radical_isSemisimple
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L] :
-- imply
  LieAlgebra.IsSemisimple K (L ⧸ LieAlgebra.radical K L) := by
-- proof
  apply levi_quotient_radical_isSemisimple


/--
[levi_split_central_kernel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma split_central_kernel
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [LieRing G] [LieAlgebra K G] [Module.Finite K G] [LieAlgebra.IsSemisimple K G]
-- given
  (q : LieHom K L G) (hq : Function.Surjective q)
  (hcentral : ∀ x ∈ q.ker, ∀ y : L, Bracket.bracket x y = 0) :
-- imply
  ∃ S : LieSubalgebra K L, LieAlgebra.IsSemisimple K S ∧
    ((q.ker : Submodule K L) + (S : Submodule K L) = ⊤) ∧
    ((q.ker : Submodule K L) ⊓ (S : Submodule K L) = ⊥) := by
-- proof
  apply levi_split_central_kernel q hq hcentral


/--
[levi_abelian_radical_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma abelian_radical_map
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L] :
-- imply
  let R := LieAlgebra.radical K L
  let V := leviHomScalarMaps (L := L) R
  let P : LieSubmodule K L V := Bracket.bracket R ⊤
  ∃ f : V, (∀ r : R, f.1 r = r) ∧ (∀ x : L, Bracket.bracket x f ∈ P) := by
-- proof
  apply levi_abelian_radical_map


/--
[levi_lie_le_range_theta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma lie_le_range_theta
  [Field K] [LieRing L] [LieAlgebra K L]
-- given
  (I : LieIdeal K L) (f : leviHomScalarMaps (L := L) I) (hI : IsLieAbelian I)
  (hf : ∀ r : I, f.1 r = r) :
-- imply
  (Bracket.bracket I (⊤ : LieSubmodule K L (leviHomScalarMaps I)) :
      LieSubmodule K L (leviHomScalarMaps I)).toSubmodule ≤
    LinearMap.range (leviTheta I f) := by
-- proof
  apply levi_lie_le_range_theta I hI f hf


/--
[levi_exists_of_abelian_radical](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma exists_of_abelian_radical
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
-- given
  (hR : IsLieAbelian (LieAlgebra.radical K L)) :
-- imply
  ∃ S : LieSubalgebra K L, LieAlgebra.IsSemisimple K S ∧
    ((LieAlgebra.radical K L : Submodule K L) + (S : Submodule K L) = ⊤) ∧
    ((LieAlgebra.radical K L : Submodule K L) ⊓ (S : Submodule K L) = ⊥) := by
-- proof
  apply levi_exists_of_abelian_radical hR


/--
[leviSubalgebraComapMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma subalgebraComapMap_surjective
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing G] [LieAlgebra K G]
-- given
  (q : LieHom K L G) (hq : Function.Surjective q) (T : LieSubalgebra K G) :
-- imply
  Function.Surjective (leviSubalgebraComapMap q T) := by
-- proof
  apply leviSubalgebraComapMap_surjective q hq T


/--
[leviSubalgebraComapKerToKer_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma subalgebraComapKerToKer_injective
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing G] [LieAlgebra K G]
-- given
  (q : LieHom K L G) (T : LieSubalgebra K G) :
-- imply
  Function.Injective (leviSubalgebraComapKerToKer q T) := by
-- proof
  apply leviSubalgebraComapKerToKer_injective q T


/--
[levi_radical_comap_semisimple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma radical_comap_semisimple
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [LieRing G] [LieAlgebra K G] [Module.Finite K G]
-- given
  (q : LieHom K L G) (hq : Function.Surjective q) (T : LieSubalgebra K G)
  [LieAlgebra.IsSemisimple K T] [LieAlgebra.IsSolvable q.ker] :
-- imply
  LieAlgebra.radical K (T.comap q) = (leviSubalgebraComapMap q T).ker := by
-- proof
  apply levi_radical_comap_semisimple q hq T


/--
[levi_derived_radical_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma derived_radical_lt
  [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
-- given
  (hR : ¬ IsLieAbelian (LieAlgebra.radical K L)) :
-- imply
  Bracket.bracket (LieAlgebra.radical K L) (LieAlgebra.radical K L) <
    LieAlgebra.radical K L := by
-- proof
  apply levi_derived_radical_lt hR


/--
[levi_quotient_derived_radical_abelian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma quotient_derived_radical_abelian
  [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L] :
-- imply
  let R := LieAlgebra.radical K L
  let D : LieIdeal K L := Bracket.bracket R R
  IsLieAbelian (LieAlgebra.radical K (L ⧸ D)) := by
-- proof
  apply levi_quotient_derived_radical_abelian


-- created on 2026-10-09
