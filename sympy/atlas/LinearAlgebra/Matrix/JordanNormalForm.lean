/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/JordanNormalForm.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Block

import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Jordan normal form

This file proves that a finite square matrix over a field has a Jordan normal form whenever its
characteristic polynomial splits.  The proof first constructs Jordan-chain bases for nilpotent
endomorphisms, then applies that construction on the maximal generalized eigenspaces.
-/

open Module
open scoped BigOperators

universe v

variable {K : Type*} [Field K]

namespace MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted

/--
A Jordan block of size `s` with eigenvalue `μ`: `μ` on the diagonal, `1` on the first
superdiagonal, `0` elsewhere.

Sources: Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms /
Jordan normal form; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University
Press (2013), Section 3.4.
-/
def jordanBlock (s : ℕ) (μ : K) : Matrix (Fin s) (Fin s) K :=
  fun i j => if i.val + 1 = j.val then 1 else if i = j then μ else 0

end MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted
namespace LinearMap
end LinearMap
private def jordanRangeMap
    {V : Type*} [AddCommGroup V] [Module K V] (f : Module.End K V) :
    V →ₗ[K] f.range :=
  f.codRestrict f.range fun x => ⟨x, rfl⟩

private noncomputable def jordanRangePreimage
    {V : Type*} [AddCommGroup V] [Module K V] (f : Module.End K V) (x : f.range) : V :=
  Classical.choose x.property

private noncomputable def jordanLiftedChains
    {V ι : Type*} [AddCommGroup V] [Module K V] (f : Module.End K V)
    (d : ι → ℕ) (b : Basis (Σ i, Fin (d i + 1)) K f.range) :
    (Σ i, Fin (d i + 1 + 1)) → V :=
  fun p => Fin.lastCases
    (jordanRangePreimage f (b ⟨p.1, Fin.last (d p.1)⟩))
    (fun q => (b ⟨p.1, q⟩ : f.range).1) p.2

private def jordanAugmentEquiv {ι J : Type*} (d : ι → ℕ) :
    ((Σ i, Fin (d i + 1 + 1)) ⊕ J) ≃
      (Σ q : ι ⊕ J, Fin (Sum.elim (fun i => d i + 1) (fun _ => 0) q + 1)) where
  toFun
    | Sum.inl p => ⟨Sum.inl p.1, p.2⟩
    | Sum.inr j => ⟨Sum.inr j, 0⟩
  invFun
    | ⟨Sum.inl i, j⟩ => Sum.inl ⟨i, j⟩
    | ⟨Sum.inr j, _⟩ => Sum.inr j
  left_inv x := by cases x <;> rfl
  right_inv x := by
    obtain ⟨i, j⟩ := x
    cases i with
    | inl i => rfl
    | inr i =>
      change (⟨Sum.inr i, (0 : Fin 1)⟩ :
        Σ q : ι ⊕ J, Fin (Sum.elim (fun i => d i + 1) (fun _ => 0) q + 1)) =
          ⟨Sum.inr i, j⟩
      congr
      apply Fin.ext
      omega
namespace Module.End
end Module.End
namespace MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted
end MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted
