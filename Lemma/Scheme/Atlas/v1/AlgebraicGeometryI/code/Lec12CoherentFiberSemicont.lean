import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec12CoherentFiberSemicont
open TensorProduct
open scoped TensorProduct


/--
[fiberDim_eq_rankAtStalk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec12CoherentFiberSemicont.lean)
-/
@[path]
lemma fiberDim_eq_rankAtStalk
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [Module.Flat R M]
  [Module.Finite R M]
  {p : PrimeSpectrum R} :
-- imply
  fiberDim M p.asIdeal = Module.rankAtStalk M p :=
-- proof
  (Module.rankAtStalk_eq p).symm

/--
[lemma25_fiber_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec12CoherentFiberSemicont.lean)
-/
@[path]
lemma lemma25_fiber_finite
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  {𝔭 : Ideal R}
  [𝔭.IsPrime] :
-- imply
  Module.Finite 𝔭.ResidueField (𝔭.ResidueField ⊗[R] M) :=
-- proof
  Module.Finite.base_change R 𝔭.ResidueField M

/--
[lemma25_fiber_zero_iff_not_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec12CoherentFiberSemicont.lean)
-/
@[path]
lemma lemma25_fiber_zero_iff_not_mem_support
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  {p : PrimeSpectrum R} :
-- imply
  fiberDim M p.asIdeal = 0 ↔ p ∉ Module.support R M := by
-- proof
  unfold fiberDim
  haveI : Module.Finite p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) :=
    Module.Finite.base_change R p.asIdeal.ResidueField M
  rw [Module.finrank_zero_iff, Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    not_nontrivial_iff_subsingleton]

/--
[lemma25_support_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec12CoherentFiberSemicont.lean)
-/
@[path]
lemma lemma25_support_isClosed
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M] :
-- imply
  IsClosed (Module.support R M) := by
-- proof
  rw [Module.support_eq_zeroLocus]
  exact PrimeSpectrum.isClosed_zeroLocus _

/--
[spanFinrank_top_eq_of_linearEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec12CoherentFiberSemicont.lean)
-/
@[path]
lemma spanFinrank_top_eq_of_linearEquiv
  {M N : Type u}
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup N]
  [Module R N]
  {e : M ≃ₗ[R] N} :
-- imply
  (⊤ : Submodule R M).spanFinrank = (⊤ : Submodule R N).spanFinrank := by
-- proof
  have h1 : Submodule.map e.toLinearMap (⊤ : Submodule R M) = ⊤ := by simp [LinearEquiv.range]
  have h2 : Submodule.map e.symm.toLinearMap (⊤ : Submodule R N) = ⊤ := by simp [LinearEquiv.range]
  have le1 : (⊤ : Submodule R N).spanRank ≤ (⊤ : Submodule R M).spanRank := by
    rw [← h1]; exact Submodule.spanRank_map_le e.toLinearMap ⊤
  have le2 : (⊤ : Submodule R M).spanRank ≤ (⊤ : Submodule R N).spanRank := by
    rw [← h2]; exact Submodule.spanRank_map_le e.symm.toLinearMap ⊤
  simp [Submodule.spanFinrank, le_antisymm le2 le1]

/--
[finrank_residueField_tensor_eq_spanFinrank_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec12CoherentFiberSemicont.lean)
-/
@[path]
lemma finrank_residueField_tensor_eq_spanFinrank_top
  {R : Type u}
  [CommRing R]
  [IsLocalRing R]
  {M : Type u}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M] :
-- imply
  Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M) = (⊤ : Submodule R M).spanFinrank := by
-- proof
  set κ := IsLocalRing.ResidueField R
  set N : Submodule R M := ⊤
  calc Module.finrank κ (κ ⊗[R] M)
    = Module.finrank κ (κ ⊗[R] ↥N) := (topEquivTensor κ R M).finrank_eq.symm
    _ = (⊤ : Submodule κ (κ ⊗[R] ↥N)).spanFinrank := Module.finrank_eq_spanFinrank_of_free
    _ = N.spanFinrank :=
      TensorProduct.spanFinrank_top_eq_of_residueField N Module.Finite.fg_top

/--
[fiberDim_eq_spanFinrank_stalk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec12CoherentFiberSemicont.lean)
-/
@[path]
lemma fiberDim_eq_spanFinrank_stalk
  {R : Type u}
  [CommRing R]
  {M : Type u}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  {𝔭 : Ideal R}
  [𝔭.IsPrime] :
-- imply
  fiberDim M 𝔭 = (⊤ : Submodule (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔭 ⊗[R] M)).spanFinrank := by
-- proof
  set R𝔭 := Localization.AtPrime 𝔭
  set M𝔭 := R𝔭 ⊗[R] M
  set κ𝔭 := 𝔭.ResidueField
  haveI : Module.Finite R𝔭 M𝔭 := Module.Finite.base_change R R𝔭 M
  haveI : SMulCommClass R R𝔭 R𝔭 := Algebra.to_smulCommClass
  have cbc : κ𝔭 ⊗[R𝔭] M𝔭 ≃ₗ[κ𝔭] κ𝔭 ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R R𝔭 κ𝔭 κ𝔭 M
  unfold fiberDim
  rw [show Module.finrank κ𝔭 (κ𝔭 ⊗[R] M) = Module.finrank κ𝔭 (κ𝔭 ⊗[R𝔭] M𝔭)
    from cbc.finrank_eq.symm]
  exact finrank_residueField_tensor_eq_spanFinrank_top

/--
[lemma25_fiber_upper_semicontinuity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec12CoherentFiberSemicont.lean)
-/
@[path]
lemma lemma25_fiber_upper_semicontinuity
  {R : Type u}
  [CommRing R]
  [IsNoetherianRing R]
  {M : Type u}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  {𝔭 𝔮 : Ideal R}
  [𝔭.IsPrime]
  [𝔮.IsPrime]
-- given
  (h : 𝔭 ≤ 𝔮) :
-- imply
  fiberDim M 𝔭 ≤ fiberDim M 𝔮 := by
-- proof
  set R𝔭 := Localization.AtPrime 𝔭
  set R𝔮 := Localization.AtPrime 𝔮
  set M𝔭 : Type u := R𝔭 ⊗[R] M
  set M𝔮 : Type u := R𝔮 ⊗[R] M
  have hsub : 𝔮.primeCompl ≤ 𝔭.primeCompl := fun x hx hmem => hx (h hmem)
  letI : Algebra R𝔮 R𝔭 :=
    IsLocalization.localizationAlgebraOfSubmonoidLe R𝔮 R𝔭 𝔮.primeCompl 𝔭.primeCompl hsub
  haveI : IsScalarTower R R𝔮 R𝔭 :=
    IsLocalization.localization_isScalarTower_of_submonoid_le R𝔮 R𝔭 𝔮.primeCompl 𝔭.primeCompl hsub
  haveI : SMulCommClass R𝔮 R𝔭 R𝔭 := Algebra.to_smulCommClass
  haveI : Module.Finite R𝔭 M𝔭 := Module.Finite.base_change R R𝔭 M
  haveI : Module.Finite R𝔮 M𝔮 := Module.Finite.base_change R R𝔮 M
  rw [fiberDim_eq_spanFinrank_stalk 𝔭, fiberDim_eq_spanFinrank_stalk 𝔮]
  have cbc := AlgebraTensorModule.cancelBaseChange R R𝔮 R𝔭 R𝔭 M
  calc (⊤ : Submodule R𝔭 M𝔭).spanFinrank
    = (⊤ : Submodule R𝔭 (R𝔭 ⊗[R𝔮] M𝔮)).spanFinrank :=
      spanFinrank_top_eq_of_linearEquiv cbc.symm
    _ = (⊤ : Submodule R𝔭 (R𝔭 ⊗[R𝔮] ↥(⊤ : Submodule R𝔮 M𝔮))).spanFinrank :=
      spanFinrank_top_eq_of_linearEquiv (topEquivTensor R𝔭 R𝔮 M𝔮).symm
    _ ≤ (⊤ : Submodule R𝔮 M𝔮).spanFinrank :=
      TensorProduct.spanFinrank_top_le_of_fg (⊤ : Submodule R𝔮 M𝔮) Module.Finite.fg_top

/--
[lemma25_locally_free_criterion_mp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec12CoherentFiberSemicont.lean)
-/
@[path]
lemma lemma25_locally_free_criterion_mp
  {R : Type u}
  [CommRing R]
  [IsNoetherianRing R]
  [IsLocalRing R]
  [IsDomain R]
  {M : Type u}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  [Module.Free R M] :
-- imply
  fiberDim M (IsLocalRing.maximalIdeal R) = Module.finrank (FractionRing R) (FractionRing R ⊗[R] M) := by
-- proof
  show Module.finrank _ _ = Module.finrank _ _
  have h1 : Module.finrank (IsLocalRing.maximalIdeal R).ResidueField
    ((IsLocalRing.maximalIdeal R).ResidueField ⊗[R] M) = Module.finrank R M :=
    Module.finrank_baseChange
  have h2 : Module.finrank (FractionRing R) (FractionRing R ⊗[R] M) = Module.finrank R M :=
    Module.finrank_baseChange
  rw [h1, h2]
/-- Reverse direction of the local-free criterion: over a local Noetherian domain, if
the fiber dimensions at the closed and generic points coincide, then `M` is free. -/


-- created on 2026-10-23
