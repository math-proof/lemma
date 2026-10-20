import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.BilinearForm.DualLattice
open scoped nonZeroDivisors
open Submodule


/--
[Submodule.isLocalizedModule_subtype_of_span_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLattice.lean)
-/
@[path]
private lemma Submodule_isLocalizedModule_subtype_of_span_eq_top_eq
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
  {M : Submodule A V}
-- given
  (hspan : Submodule.span K (M : Set V) = ⊤) :
-- imply
  IsLocalizedModule (A⁰) M.subtype where
    map_units s := by
-- proof
  apply Submodule.isLocalizedModule_subtype_of_span_eq_top M hspan

/--
[LinearMap.BilinForm.dualSubmoduleToDual_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLattice.lean)
-/
@[path]
private lemma LinearMap_BilinForm_dualSubmoduleToDual_surjective_eq
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V] [IsDomain A] [FiniteDimensional K V]
  {B : LinearMap.BilinForm K V}
  {M : Submodule A V}
-- given
  (hB : B.Nondegenerate)
  (hspan : Submodule.span K (M : Set V) = ⊤) :
-- imply
  Function.Surjective (B.dualSubmoduleToDual M) := by
-- proof
  apply LinearMap.BilinForm.dualSubmoduleToDual_surjective B hB M hspan

/--
[LinearMap.BilinForm.dualSubmoduleToDual_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLattice.lean)
-/
@[path]
private lemma LinearMap_BilinForm_dualSubmoduleToDual_bijective_eq
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V] [IsDomain A] [FiniteDimensional K V]
  {B : LinearMap.BilinForm K V}
  {M : Submodule A V}
-- given
  (hB : B.Nondegenerate)
  (hspan : Submodule.span K (M : Set V) = ⊤) :
-- imply
  Function.Bijective (B.dualSubmoduleToDual M) := by
-- proof
  apply LinearMap.BilinForm.dualSubmoduleToDual_bijective B hB M hspan

/--
[LinearMap.BilinForm.dualSubmodule_fg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLattice.lean)
-/
@[path]
private lemma LinearMap_BilinForm_dualSubmodule_fg_eq
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V] [IsDomain A] [IsNoetherianRing A]
  {B : LinearMap.BilinForm K V}
  {M : Submodule A V} [Module.Finite A M]
-- given
  (hB : B.Nondegenerate)
  (hspan : Submodule.span K (M : Set V) = ⊤) :
-- imply
  (B.dualSubmodule M).FG := by
-- proof
  apply LinearMap.BilinForm.dualSubmodule_fg B hB M hspan

/--
[LinearMap.BilinForm.dualSubmodule_span_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLattice.lean)
-/
@[path]
private lemma LinearMap_BilinForm_dualSubmodule_span_eq_top_eq
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
  {B : LinearMap.BilinForm K V}
  {M : Submodule A V}
-- given
  (hfg : M.FG) :
-- imply
  Submodule.span K (B.dualSubmodule M : Set V) = ⊤ := by
-- proof
  apply LinearMap.BilinForm.dualSubmodule_span_eq_top B M hfg

/--
[LinearMap.BilinForm.dualSubmodule_isLattice](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLattice.lean)
-/
@[path]
private lemma LinearMap_BilinForm_dualSubmodule_isLattice_eq
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V] [IsDomain A] [IsNoetherianRing A]
  {B : LinearMap.BilinForm K V}
  {M : Submodule A V} [Submodule.IsLattice K M]
-- given
  (hB : B.Nondegenerate) :
-- imply
  Submodule.IsLattice K (B.dualSubmodule M) where
    fg := by
-- proof
  apply LinearMap.BilinForm.dualSubmodule_isLattice B hB M

/--
[LinearMap.BilinForm.dualSubmodule_isLattice_and_dualSubmoduleToDual_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLattice.lean)
-/
@[path]
private lemma LinearMap_BilinForm_dualSubmodule_isLattice_and_dualSubmoduleToDual_bijective_eq
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V] [IsDomain A] [FiniteDimensional K V] [IsNoetherianRing A]
  {B : LinearMap.BilinForm K V}
  {M : Submodule A V} [Submodule.IsLattice K M]
-- given
  (hB : B.Nondegenerate) :
-- imply
  Submodule.IsLattice K (B.dualSubmodule M) ∧
    Function.Bijective (B.dualSubmoduleToDual M) := by
-- proof
  apply LinearMap.BilinForm.dualSubmodule_isLattice_and_dualSubmoduleToDual_bijective B hB M


-- created on 2026-10-20
