import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.LinearAlgebra.BilinearForm.DualLatticeReflexive
open LinearMap (BilinForm)
open Module


/--
[LinearMap.BilinForm.dualSubmodule_flip_dualSubmodule_of_isLattice](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLatticeReflexive.lean)
-/
@[path]
lemma LinearMap.BilinForm.dualSubmodule_flip_dualSubmodule_of_isLattice
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V] [FiniteDimensional K V] [IsDomain A]
  {B : BilinForm K V}
  {M : Submodule A V} [Submodule.IsLattice K M] [Module.IsReflexive A M]
-- given
  (hB : B.Nondegenerate) :
-- imply
  B.flip.dualSubmodule (B.dualSubmodule M) = M := by
-- proof
  apply le_antisymm
  · intro x hx
    -- Identify `D(M)` with the module dual via the pairing.
    let e : (B.dualSubmodule M) ≃ₗ[A] Module.Dual A M :=
      B.dualSubmoduleLinearEquiv hB M Submodule.IsLattice.span_eq_top
    -- The functional on `D(M)` cut out by `x` against `B.flip`.
    let φ : Module.Dual A (B.dualSubmodule M) :=
      B.flip.dualSubmoduleToDual (B.dualSubmodule M) ⟨x, hx⟩
    -- Transport it to the double dual and recover a lattice element by reflexivity.
    obtain ⟨m, hm⟩ :=
      (Module.bijective_dual_eval A M).2 (φ.comp e.symm.toLinearMap)
    have key : ∀ g : Module.Dual A M, φ (e.symm g) = g m := fun g => by
      have hgm := LinearMap.congr_fun hm g
      rwa [Module.Dual.eval_apply, LinearMap.comp_apply] at hgm
    -- It suffices to show `x = m`, comparing in the flip-double dual.
    have hspan₂ : Submodule.span K (B.dualSubmodule M : Set V) = ⊤ :=
      B.dualSubmodule_span_eq_top M Submodule.IsLattice.fg
    have hinj := B.flip.dualSubmoduleToDual_injective hB.flip
      (B.dualSubmodule M) hspan₂
    have hme : (m : V) ∈ B.flip.dualSubmodule (B.dualSubmodule M) :=
      (BilinForm.le_flip_dualSubmodule (B := B)).mpr le_rfl m.2
    have hfun : (B.flip.dualSubmoduleToDual (B.dualSubmodule M)) ⟨x, hx⟩ =
      (B.flip.dualSubmoduleToDual (B.dualSubmodule M)) ⟨(m : V), hme⟩ := by
      apply LinearMap.ext
      intro z
      have h1 : φ z = (e z) m := by
        have h := key (e z)
        rwa [LinearEquiv.symm_apply_apply] at h
      have h2 : (e z) m =
        B.flip.dualSubmoduleParing ⟨(m : V), hme⟩ z := by
        apply FaithfulSMul.algebraMap_injective A K
        change algebraMap A K (B.dualSubmoduleParing z m) = _
        rw [BilinForm.dualSubmoduleParing_spec, BilinForm.dualSubmoduleParing_spec,
          BilinForm.flip_apply]
      have h3 : ((B.flip.dualSubmoduleToDual (B.dualSubmodule M)) ⟨x, hx⟩) z =
        φ z := rfl
      have h4 : ((B.flip.dualSubmoduleToDual (B.dualSubmodule M)) ⟨(m : V), hme⟩) z =
        B.flip.dualSubmoduleParing ⟨(m : V), hme⟩ z := rfl
      rw [h3, h4, h1, h2]
    have hveq : x = (m : V) := congrArg Subtype.val (hinj hfun)
    rwa [hveq]
  · exact (BilinForm.le_flip_dualSubmodule (B := B)).mpr le_rfl

/--
[LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_isLattice](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLatticeReflexive.lean)
-/
@[path]
lemma LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_isLattice
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V] [FiniteDimensional K V] [IsDedekindDomain A]
  {B : BilinForm K V}
  {M : Submodule A V} [Submodule.IsLattice K M]
-- given
  (hB : B.Nondegenerate)
  (hBsymm : B.IsSymm) :
-- imply
  B.dualSubmodule (B.dualSubmodule M) = M := by
-- proof
  have : Module.IsTorsionFree A V :=
    Module.IsTorsionFree.trans_faithfulSMul A K V
  have : Module.FinitePresentation A M :=
    Module.finitePresentation_of_finite A M
  have : Module.Projective A M :=
    Module.Flat.projective_of_finitePresentation
  have hflip : B.flip = B := BilinForm.isSymm_iff_flip.mp hBsymm
  have h := B.dualSubmodule_flip_dualSubmodule_of_isLattice hB M
  rwa [hflip] at h


-- created on 2026-10-20
-- updated on 2026-10-26
