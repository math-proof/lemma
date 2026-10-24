import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.BilinearForm.DualLattice
open scoped nonZeroDivisors
open Submodule


/--
[Submodule.isLocalizedModule_subtype_of_span_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLattice.lean)
-/
@[path]
lemma Submodule.isLocalizedModule_subtype_of_span_eq_top
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
  {M : Submodule A V}
-- given
  (hspan : Submodule.span K (M : Set V) = ⊤) :
-- imply
  IsLocalizedModule (A⁰) M.subtype where
    map_units s := by
-- proof
  rw [← (Algebra.lsmul A (A := K) A V).commutes]
  exact (IsLocalization.map_units K s).map _
  surj y := by
    have hy : y ∈ Submodule.span K (M : Set V) := hspan ▸ trivial
    induction hy using Submodule.span_induction with
    | mem x hx =>
      exact ⟨⟨⟨x, hx⟩, 1⟩, by simp⟩
    | zero =>
      exact ⟨⟨0, 1⟩, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨⟨a, s⟩, hs⟩ := hx
      obtain ⟨⟨b, t⟩, ht⟩ := hz
      refine ⟨⟨t • a + s • b, s * t⟩, ?_⟩
      simp only [Submonoid.smul_def] at hs ht ⊢
      change ((s * t : A⁰) : A) • (x + z) = ↑(t • a + s • b)
      simp only [Submonoid.coe_mul]
      rw [smul_add]
      change ((s : A) * (t : A)) • x + ((s : A) * (t : A)) • z =
        (t : A) • ((a : M) : V) + (s : A) • ((b : M) : V)
      congr 1
      · rw [mul_comm, mul_smul, hs]
        rfl
      · rw [mul_smul, ht]
        rfl
    | smul c x _ hx =>
      obtain ⟨⟨a, s⟩, hs⟩ := hx
      obtain ⟨⟨r, d⟩, hd⟩ := IsLocalization.surj (A⁰) c
      refine ⟨⟨r • a, s * d⟩, ?_⟩
      simp only [Submonoid.smul_def] at hs ⊢
      have hdc : algebraMap A K (d : A) * c = algebraMap A K r := by
        simpa [mul_comm] using hd
      change ((s * d : A⁰) : A) • (c • x) = (r : A) • ((a : M) : V)
      rw [← IsScalarTower.algebraMap_smul K] at hs ⊢
      simp only [Submonoid.coe_mul, map_mul, smul_smul] at hs ⊢
      rw [mul_assoc, hdc, mul_comm (algebraMap A K (s : A)) _, mul_smul, hs]
      rw [IsScalarTower.algebraMap_smul]
      rfl
  exists_of_eq h := ⟨1, by simpa [Submonoid.smul_def] using h⟩

/--
[LinearMap.BilinForm.dualSubmoduleToDual_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLattice.lean)
-/
@[path]
lemma LinearMap.BilinForm.dualSubmoduleToDual_surjective
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V] [IsDomain A] [FiniteDimensional K V]
  {B : LinearMap.BilinForm K V}
  {M : Submodule A V}
-- given
  (hB : B.Nondegenerate)
  (hspan : Submodule.span K (M : Set V) = ⊤) :
-- imply
  Function.Surjective (B.dualSubmoduleToDual M) := by
-- proof
  let _ : IsLocalizedModule A⁰ M.subtype :=
    Submodule.isLocalizedModule_subtype_of_span_eq_top M hspan
  intro f
  let fK : V →ₗ[K] K :=
    IsLocalizedModule.mapExtendScalars A⁰ M.subtype (Algebra.linearMap A K) K f
  set x := (B.toDual hB).symm fK with hx
  have key : ∀ y : M, B x (y : V) = algebraMap A K (f y) := fun y => by
    rw [hx, LinearMap.BilinForm.apply_toDual_symm_apply]
    change (IsLocalizedModule.map A⁰ M.subtype (Algebra.linearMap A K) f) (M.subtype y) =
      algebraMap A K (f y)
    simpa using IsLocalizedModule.map_apply A⁰ M.subtype (Algebra.linearMap A K) f y
  have hmem : x ∈ B.dualSubmodule M := fun y hy =>
    Submodule.mem_one.mpr ⟨f ⟨y, hy⟩, by simpa using (key ⟨y, hy⟩).symm⟩
  refine ⟨⟨x, hmem⟩, ?_⟩
  ext y
  apply FaithfulSMul.algebraMap_injective A K
  change algebraMap A K (B.dualSubmoduleParing ⟨x, hmem⟩ y) = algebraMap A K (f y)
  rw [LinearMap.BilinForm.dualSubmoduleParing_spec, key y]

/--
[LinearMap.BilinForm.dualSubmoduleToDual_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLattice.lean)
-/
@[path]
lemma LinearMap.BilinForm.dualSubmoduleToDual_bijective
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V] [IsDomain A] [FiniteDimensional K V]
  {B : LinearMap.BilinForm K V}
  {M : Submodule A V}
-- given
  (hB : B.Nondegenerate)
  (hspan : Submodule.span K (M : Set V) = ⊤) :
-- imply
  Function.Bijective (B.dualSubmoduleToDual M) :=
-- proof
  ⟨B.dualSubmoduleToDual_injective hB M hspan,
    B.dualSubmoduleToDual_surjective hB M hspan⟩

/--
[LinearMap.BilinForm.dualSubmodule_fg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLattice.lean)
-/
@[path]
lemma LinearMap.BilinForm.dualSubmodule_fg
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V] [IsDomain A] [IsNoetherianRing A]
  {B : LinearMap.BilinForm K V}
  {M : Submodule A V} [Module.Finite A M]
-- given
  (hB : B.Nondegenerate)
  (hspan : Submodule.span K (M : Set V) = ⊤) :
-- imply
  (B.dualSubmodule M).FG := by
-- proof
  rw [← Module.Finite.iff_fg]
  exact Module.Finite.of_injective (B.dualSubmoduleToDual M)
    (B.dualSubmoduleToDual_injective hB M hspan)

/--
[LinearMap.BilinForm.dualSubmodule_span_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLattice.lean)
-/
@[path]
lemma LinearMap.BilinForm.dualSubmodule_span_eq_top
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
  {B : LinearMap.BilinForm K V}
  {M : Submodule A V}
-- given
  (hfg : M.FG) :
-- imply
  Submodule.span K (B.dualSubmodule M : Set V) = ⊤ := by
-- proof
  rw [eq_top_iff]
  intro x _
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples A⁰ s (fun y => B x y)
  have hBsmul : ∀ y, B ((d : A) • x) y = (d : A) • B x y := fun y => by
    rw [← IsScalarTower.algebraMap_smul K]
    rw [map_smul, LinearMap.smul_apply, IsScalarTower.algebraMap_smul K]
  have hle : M ≤
    (1 : Submodule A K).comap ((B ((d : A) • x)).restrictScalars A) := by
    rw [← hs, Submodule.span_le]
    intro y hy
    change B ((d : A) • x) y ∈ (1 : Submodule A K)
    obtain ⟨a, ha⟩ := hd y (Finset.mem_coe.mp hy)
    exact Submodule.mem_one.mpr ⟨a, by simpa using ha.trans (hBsmul y).symm⟩
  have hmem : (d : A) • x ∈ B.dualSubmodule M := fun y hy => hle hy
  have hspanmem : (d : A) • x ∈ Submodule.span K (B.dualSubmodule M : Set V) :=
    Submodule.subset_span hmem
  obtain ⟨u, hu⟩ := IsLocalization.map_units K d
  have hdx : (d : A) • x = (u : K) • x := by
    rw [hu, IsScalarTower.algebraMap_smul K]
  have hx : x = ((u⁻¹ : Kˣ) : K) • ((d : A) • x) := by
    rw [hdx, ← mul_smul, Units.inv_mul, one_smul]
  rw [hx]
  exact Submodule.smul_mem _ _ hspanmem

/--
[LinearMap.BilinForm.dualSubmodule_isLattice](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLattice.lean)
-/
@[path]
lemma LinearMap.BilinForm.dualSubmodule_isLattice
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V] [IsDomain A] [IsNoetherianRing A]
  {B : LinearMap.BilinForm K V}
  {M : Submodule A V} [Submodule.IsLattice K M]
-- given
  (hB : B.Nondegenerate) :
-- imply
  Submodule.IsLattice K (B.dualSubmodule M) where
    fg :=
-- proof
  B.dualSubmodule_fg hB M IsLattice.span_eq_top
    span_eq_top := B.dualSubmodule_span_eq_top M IsLattice.fg

/--
[LinearMap.BilinForm.dualSubmodule_isLattice_and_dualSubmoduleToDual_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLattice.lean)
-/
@[path]
lemma LinearMap.BilinForm.dualSubmodule_isLattice_and_dualSubmoduleToDual_bijective
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V] [IsDomain A] [FiniteDimensional K V] [IsNoetherianRing A]
  {B : LinearMap.BilinForm K V}
  {M : Submodule A V} [Submodule.IsLattice K M]
-- given
  (hB : B.Nondegenerate) :
-- imply
  Submodule.IsLattice K (B.dualSubmodule M) ∧
    Function.Bijective (B.dualSubmoduleToDual M) :=
-- proof
  ⟨B.dualSubmodule_isLattice hB M,
    B.dualSubmoduleToDual_bijective hB M IsLattice.span_eq_top⟩


-- created on 2026-10-20
-- updated on 2026-10-23
