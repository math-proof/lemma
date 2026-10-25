/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteAbelianDual.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Algebra.Group.AddChar
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality


namespace MathlibExt.GroupTheory.FiniteAbelianDualWanted

open scoped DirectSum

/-!
# Dual groups of finite abelian groups

The dual-group cardinality, basis, and double-dual statements are
`AddChar.card_eq`, `AddChar.complexBasis`, and `AddChar.doubleDualEquiv`; the
(non-canonical) self-duality of a finite abelian group and the product
decomposition of the dual are recorded here.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "dual groups" (reference-only, no Lean formalization);
J.-P. Serre, Linear Representations of Finite Groups, GTM 42 (listed by the
Wanted entry); K. Conrad, Characters of finite abelian groups,
https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf, Lemma 3.12 and
Theorem 3.13.
-/

def dual_precomp {α β : Type*} [AddCommGroup α] [AddCommGroup β]
    (e : α ≃+ β) : AddChar β ℂ ≃+ AddChar α ℂ where
  toFun ψ := ψ.compAddMonoidHom e.toAddMonoidHom
  invFun ψ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  left_inv ψ := by
    ext x
    simp
  right_inv ψ := by
    ext x
    simp
  map_add' ψ χ := by
    ext x
    rfl

def dual_directSumHom {ι : Type*} [DecidableEq ι]
    {G : ι → Type*} [∀ i, AddCommGroup (G i)] :
    (∀ i, AddChar (G i) ℂ) →+ AddChar (⨁ i, G i) ℂ := by
  refine
    { toFun := AddChar.directSum
      map_zero' := ?_
      map_add' := ?_ }
  · ext x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      simp only [AddChar.directSum_apply, DirectSum.toAddMonoid_of]
      rfl
    | add x y hx hy => simp [AddChar.map_add_eq_mul, hx, hy]
  · intro ψ χ
    ext x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [AddChar.add_apply]
      simp only [AddChar.directSum_apply, DirectSum.toAddMonoid_of,
        Pi.add_apply, AddChar.toAddMonoidHomEquiv_apply, AddChar.add_apply]
      rfl
    | add x y hx hy =>
      simp only [AddChar.map_add_eq_mul, AddChar.add_apply, hx, hy]

noncomputable def dual_zmodFamilyHom {ι : Type*} [DecidableEq ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] :
    (⨁ i, ZMod (n i)) →+ (∀ i, AddChar (ZMod (n i)) ℂ) where
  toFun u i := AddChar.zmodAddEquiv (u i)
  map_zero' := by
    funext i
    exact map_zero AddChar.zmodAddEquiv
  map_add' u v := by
    funext i
    exact map_add AddChar.zmodAddEquiv (u i) (v i)

noncomputable def dual_zmodDirectSumHom {ι : Type*} [DecidableEq ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] :
    (⨁ i, ZMod (n i)) →+ AddChar (⨁ i, ZMod (n i)) ℂ :=
  dual_directSumHom.comp (dual_zmodFamilyHom n)

end MathlibExt.GroupTheory.FiniteAbelianDualWanted
