import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.LinearAlgebra.PerfectPairing.DualBasis
open Module
open LinearMap.IsPerfPair


namespace LinearMap.IsPerfPair

/--
[dualBasis_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/PerfectPairing/DualBasis.lean)
-/
@[path]
lemma dualBasis_apply
  [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [DecidableEq ι] [Finite ι]
  {B : M →ₗ[A] N →ₗ[A] A} [B.IsPerfPair]
  {b : Basis ι A N}
  {i j : ι} :
-- imply
  B (dualBasis B b i) (b j) = if j = i then 1 else 0 := by
-- proof
  rw [dualBasis, Basis.map_apply, ← LinearMap.toPerfPair_apply,
    LinearEquiv.apply_symm_apply, Basis.dualBasis_apply_self]

end LinearMap.IsPerfPair

namespace LinearMap.IsPerfPair

/--
[eq_dualBasis_of](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/PerfectPairing/DualBasis.lean)
-/
@[path]
lemma eq_dualBasis_of
  [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [DecidableEq ι] [Finite ι]
  {B : M →ₗ[A] N →ₗ[A] A} [B.IsPerfPair]
  {b : Basis ι A N}
  {b' : Basis ι A M}
-- given
  (h : ∀ i j, B (b' i) (b j) = if j = i then 1 else 0) :
-- imply
  b' = dualBasis B b := by
-- proof
  refine Basis.eq_of_apply_eq fun i => ?_
  have key : B.toPerfPair (b' i) = b.dualBasis i := by
    apply b.ext
    intro j
    rw [LinearMap.toPerfPair_apply, h i j, b.dualBasis_apply_self]
  calc b' i = B.toPerfPair.symm (B.toPerfPair (b' i)) :=
    (B.toPerfPair.symm_apply_apply (b' i)).symm
    _ = B.toPerfPair.symm (b.dualBasis i) := by rw [key]
    _ = dualBasis B b i := by simp only [dualBasis, Basis.map_apply]

end LinearMap.IsPerfPair

namespace LinearMap.IsPerfPair

/--
[exists_dualBasis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/PerfectPairing/DualBasis.lean)
-/
@[path]
lemma exists_dualBasis
  [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [DecidableEq ι] [Finite ι]
  {B : M →ₗ[A] N →ₗ[A] A} [B.IsPerfPair]
  {b : Basis ι A N} :
-- imply
  ∃ b' : Basis ι A M, ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 :=
-- proof
  ⟨dualBasis B b, fun i j => dualBasis_apply B b i j⟩

end LinearMap.IsPerfPair

namespace LinearMap.IsPerfPair

/--
[existsUnique_dualBasis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/PerfectPairing/DualBasis.lean)
-/
@[path]
lemma existsUnique_dualBasis
  [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [DecidableEq ι] [Finite ι]
  {B : M →ₗ[A] N →ₗ[A] A} [B.IsPerfPair]
  {b : Basis ι A N} :
-- imply
  ∃! b' : Basis ι A M, ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 := by
-- proof
  refine ⟨dualBasis B b, fun i j => dualBasis_apply B b i j, fun b' hb' => ?_⟩
  exact eq_dualBasis_of B b b' hb'

end LinearMap.IsPerfPair


-- created on 2026-10-20
-- updated on 2026-10-26
