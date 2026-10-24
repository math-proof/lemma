import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.GeneralPosition
open Function
open scoped Affine LinearAlgebra.Projectivization
open Projectivization


namespace Projectivization

/--
[Independent.isGeneralPosition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/GeneralPosition.lean)
-/
@[path]
lemma Independent.isGeneralPosition
  {k : Type u} [DivisionRing k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {p : ι → ℙ k V}
  {d : ℕ}
-- given
  (hp : Independent p) :
-- imply
  IsGeneralPosition d p := by
-- proof
  intro s _
  rw [independent_iff] at hp ⊢
  simpa [Finset.restrict_def, Function.comp_def] using
    hp.comp (fun i : s ↦ (i : ι)) Subtype.val_injective

end Projectivization

/--
[AffineIndependent.isGeneralPosition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/GeneralPosition.lean)
-/
@[path]
lemma AffineIndependent.isGeneralPosition
  {k : Type u} [DivisionRing k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {P : Type w} [AffineSpace V P]
  {p : ι → P}
  {d : ℕ}
-- given
  (hp : AffineIndependent k p) :
-- imply
  IsGeneralPosition k d p :=
-- proof
  fun s _ ↦ hp.subtype s

/--
[IsGeneralPosition.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/GeneralPosition.lean)
-/
@[path]
lemma IsGeneralPosition.mono
  {k : Type u} [DivisionRing k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {P : Type w} [AffineSpace V P]
  {d e : ℕ}
  {p : ι → P}
-- given
  (hp : IsGeneralPosition k e p)
  (hde : d ≤ e) :
-- imply
  IsGeneralPosition k d p :=
-- proof
  fun s hs ↦ hp s (hs.trans (Nat.add_le_add_right hde 1))
section Examples

namespace Projectivization

/--
[IsGeneralPosition.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/GeneralPosition.lean)
-/
@[path]
lemma IsGeneralPosition.mono
  {k : Type u} [DivisionRing k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {P : Type w} [AffineSpace V P]
  {d e : ℕ}
  {p : ι → P}
-- given
  (hp : IsGeneralPosition k e p)
  (hde : d ≤ e) :
-- imply
  IsGeneralPosition k d p :=
-- proof
  fun s hs ↦ hp s (hs.trans (Nat.add_le_add_right hde 1))

end Projectivization


-- created on 2026-10-20
-- updated on 2026-10-23
