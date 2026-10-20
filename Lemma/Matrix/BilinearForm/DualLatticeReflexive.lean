import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.BilinearForm.DualLatticeReflexive
open LinearMap (BilinForm)
open Module


/--
[LinearMap.BilinForm.dualSubmodule_flip_dualSubmodule_of_isLattice](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLatticeReflexive.lean)
-/
@[path]
private lemma LinearMap_BilinForm_dualSubmodule_flip_dualSubmodule_of_isLattice_eq
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V] [FiniteDimensional K V] [IsDomain A]
  {B : BilinForm K V}
  {M : Submodule A V} [Submodule.IsLattice K M] [Module.IsReflexive A M]
-- given
  (hB : B.Nondegenerate) :
-- imply
  B.flip.dualSubmodule (B.dualSubmodule M) = M := by
-- proof
  apply LinearMap.BilinForm.dualSubmodule_flip_dualSubmodule_of_isLattice B hB M

/--
[LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_isLattice](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLatticeReflexive.lean)
-/
@[path]
private lemma LinearMap_BilinForm_dualSubmodule_dualSubmodule_of_isLattice_eq
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V] [FiniteDimensional K V] [IsDedekindDomain A]
  {B : BilinForm K V}
  {M : Submodule A V} [Submodule.IsLattice K M]
-- given
  (hB : B.Nondegenerate)
  (hBsymm : B.IsSymm) :
-- imply
  B.dualSubmodule (B.dualSubmodule M) = M := by
-- proof
  apply LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_isLattice B hB hBsymm M


-- created on 2026-10-20
