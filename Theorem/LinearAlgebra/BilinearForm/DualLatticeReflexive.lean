/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLatticeReflexive.lean -/

import Def.LinearAlgebra.BilinearForm.DualLattice
import Lemma.Matrix.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.TorsionFree
open LinearMap (BilinForm)
open Module

variable {A K V : Type*} [CommRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V]
  [IsScalarTower A K V]


