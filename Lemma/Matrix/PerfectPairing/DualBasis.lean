import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.PerfectPairing.DualBasis
open Module
open LinearMap.IsPerfPair


/--
[dualBasis_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/PerfectPairing/DualBasis.lean)
-/
@[path]
private lemma dualBasis_apply_eq
  [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [DecidableEq ι] [Finite ι]
  {B : M →ₗ[A] N →ₗ[A] A} [B.IsPerfPair]
  {b : Basis ι A N}
  {i j : ι} :
-- imply
  B (dualBasis B b i) (b j) = if j = i then 1 else 0 := by
-- proof
  apply LinearMap.IsPerfPair.dualBasis_apply B b i j

/--
[eq_dualBasis_of](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/PerfectPairing/DualBasis.lean)
-/
@[path]
private lemma eq_dualBasis_of_eq
  [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [DecidableEq ι] [Finite ι]
  {B : M →ₗ[A] N →ₗ[A] A} [B.IsPerfPair]
  {b : Basis ι A N}
  {b' : Basis ι A M}
-- given
  (h : ∀ i j, B (b' i) (b j) = if j = i then 1 else 0) :
-- imply
  b' = dualBasis B b := by
-- proof
  apply LinearMap.IsPerfPair.eq_dualBasis_of B b b' h

/--
[exists_dualBasis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/PerfectPairing/DualBasis.lean)
-/
@[path]
private lemma exists_dualBasis_eq
  [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [DecidableEq ι] [Finite ι]
  {B : M →ₗ[A] N →ₗ[A] A} [B.IsPerfPair]
  {b : Basis ι A N} :
-- imply
  ∃ b' : Basis ι A M, ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 := by
-- proof
  apply LinearMap.IsPerfPair.exists_dualBasis B b

/--
[existsUnique_dualBasis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/PerfectPairing/DualBasis.lean)
-/
@[path]
private lemma existsUnique_dualBasis_eq
  [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [DecidableEq ι] [Finite ι]
  {B : M →ₗ[A] N →ₗ[A] A} [B.IsPerfPair]
  {b : Basis ι A N} :
-- imply
  ∃! b' : Basis ι A M, ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 := by
-- proof
  apply LinearMap.IsPerfPair.existsUnique_dualBasis B b


-- created on 2026-10-20
