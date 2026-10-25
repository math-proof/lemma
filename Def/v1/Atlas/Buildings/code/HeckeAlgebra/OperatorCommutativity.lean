/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/OperatorCommutativity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Lemma.List.Any_And_IsReduced_EraseIdx.of.LtLengthMulWordProdSimple_Length_WordProd.IsReduced
import Lemma.Int.LengthMulMulSimpleSimple.gt.LengthMulSimple.of.GtLengthMul_Simple_Length.LtLengthMulSimple_Length
import Def.v1.Atlas.Buildings.code.HeckeAlgebra.Generic.Part2
open scoped Classical


namespace HeckeAlgebra

variable {B : Type*} [DecidableEq B] [Fintype B]
  {M : CoxeterMatrix B} {R : Type*} [CommRing R]


/-- Left-multiplication operator $λ_s$ on the basis: $λ_s(T_w) = T_{sw}$ when
$\ell(sw) > \ell(w)$ and $λ_s(T_w) = a_s T_w + b_s T_{sw}$ otherwise. -/
noncomputable def lambdaOnBasis (cs : CoxeterSystem M M.Group)
    (a b : B → R) (s : B) (w : M.Group) : M.Group →₀ R :=
  if cs.length (cs.simple s * w) > cs.length w then
    Finsupp.single (cs.simple s * w) 1
  else
    Finsupp.single w (a s) + Finsupp.single (cs.simple s * w) (b s)

/-- Right-multiplication operator $ρ_t$ on the basis: $ρ_t(T_w) = T_{wt}$ when
$\ell(wt) > \ell(w)$ and $ρ_t(T_w) = a_t T_w + b_t T_{wt}$ otherwise. -/
noncomputable def rhoOnBasis (cs : CoxeterSystem M M.Group)
    (a b : B → R) (t : B) (w : M.Group) : M.Group →₀ R :=
  if cs.length (w * cs.simple t) > cs.length w then
    Finsupp.single (w * cs.simple t) 1
  else
    Finsupp.single w (a t) + Finsupp.single (w * cs.simple t) (b t)

/-- Linear extension of `lambdaOnBasis` to the free $R$-module $R[W]$. -/
noncomputable def lambdaLift (cs : CoxeterSystem M M.Group)
    (a b : B → R) (s : B) : (M.Group →₀ R) →ₗ[R] (M.Group →₀ R) :=
  Finsupp.linearCombination R (lambdaOnBasis cs a b s)

/-- Linear extension of `rhoOnBasis` to the free $R$-module $R[W]$. -/
noncomputable def rhoLift (cs : CoxeterSystem M M.Group)
    (a b : B → R) (t : B) : (M.Group →₀ R) →ₗ[R] (M.Group →₀ R) :=
  Finsupp.linearCombination R (rhoOnBasis cs a b t)

end HeckeAlgebra
