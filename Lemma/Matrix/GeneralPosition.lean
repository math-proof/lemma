import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.GeneralPosition
open Function
open scoped Affine LinearAlgebra.Projectivization
open Projectivization


/--
[AffineIndependent.isGeneralPosition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/GeneralPosition.lean)
-/
@[path]
private lemma AffineIndependent_isGeneralPosition_eq
  {k : Type u} [DivisionRing k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {P : Type w} [AffineSpace V P]
  {p : ι → P}
  {d : ℕ}
-- given
  (hp : AffineIndependent k p) :
-- imply
  IsGeneralPosition k d p := by
-- proof
  apply AffineIndependent.isGeneralPosition hp d

/--
[IsGeneralPosition.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/GeneralPosition.lean)
-/
@[path]
private lemma IsGeneralPosition_mono_eq
  {k : Type u} [DivisionRing k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {P : Type w} [AffineSpace V P]
  {d e : ℕ}
  {p : ι → P}
-- given
  (hp : IsGeneralPosition k e p)
  (hde : d ≤ e) :
-- imply
  IsGeneralPosition k d p := by
-- proof
  apply IsGeneralPosition.mono hp hde

/--
[Independent.isGeneralPosition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/GeneralPosition.lean)
-/
@[path]
private lemma Independent_isGeneralPosition_eq
  {k : Type u} [DivisionRing k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {P : Type w}
  {p : ι → ℙ k V}
  {d : ℕ}
-- given
  (hp : Independent p) :
-- imply
  IsGeneralPosition d p := by
-- proof
  apply Projectivization.Independent.isGeneralPosition hp d

/--
[IsGeneralPosition.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/GeneralPosition.lean)
-/
@[path]
private lemma Projectivization_IsGeneralPosition_mono_eq
  {k : Type u} [DivisionRing k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {P : Type w} [AffineSpace V P]
  {d e : ℕ}
  {p : ι → P}
-- given
  (hp : IsGeneralPosition k e p)
  (hde : d ≤ e) :
-- imply
  IsGeneralPosition k d p := by
-- proof
  apply Projectivization.IsGeneralPosition.mono hp hde


-- created on 2026-10-20
