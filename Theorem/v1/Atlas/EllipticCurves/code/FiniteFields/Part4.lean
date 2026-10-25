/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Data.Nat.Prime.Basic
import Structure.v1.Atlas.EllipticCurves.code.FiniteFields


section Theorem_3_15

open Polynomial IntermediateField

/-- Auxiliary lemma for Theorem 3.15: for an integral element `α` of `E/F`,
the order of `AdjoinRoot.root (minpoly F α)` equals `orderOf α`, via the
ring isomorphism between `F[x]/(minpoly α)` and `F(α)`. -/
lemma orderOf_adjoinRoot_root_eq_orderOf (F : Type*) [Field F]
    (E : Type*) [Field E] [Algebra F E]
    (α : E) (hint : IsIntegral F α) :
    orderOf (AdjoinRoot.root (minpoly F α)) = orderOf α := by
  let e := adjoinRootEquivAdjoin F hint
  let incl : ↥(F⟮α⟯) →+* E := (IntermediateField.val (F⟮α⟯)).toRingHom
  let φ : AdjoinRoot (minpoly F α) →+* E := incl.comp e.toRingEquiv.toRingHom
  have hφ_inj : Function.Injective φ := by
    intro x y h; exact e.toRingEquiv.injective (Subtype.val_injective h)
  have hφ_root : φ (AdjoinRoot.root (minpoly F α)) = α := by
    show incl (e (AdjoinRoot.root (minpoly F α))) = α
    rw [adjoinRootEquivAdjoin_apply_root]; rfl
  conv_rhs => rw [← hφ_root]
  exact (orderOf_injective φ.toMonoidHom hφ_inj _).symm

/-- If `g` is a unit of `𝔽_{p^n}` of order `p^n - 1`, then `g` generates the
multiplicative group of `𝔽_{p^n}` and `𝔽_p(g) = 𝔽_{p^n}`. -/
lemma adjoin_top_of_unit_generator (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 0 < n)
    (g : (GaloisField p n)ˣ) (hg : orderOf g = p ^ n - 1) :
    (ZMod p)⟮(g : GaloisField p n)⟯ = ⊤ := by
  classical
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  set α := (g : GaloisField p n)
  rw [eq_top_iff]; intro x _
  by_cases hx : x = 0
  · rw [hx]; exact (ZMod p)⟮α⟯.zero_mem
  · have hord_u : orderOf g = Fintype.card (GaloisField p n)ˣ := by
      rw [hg, Fintype.card_eq_nat_card, Nat.card_units, GaloisField.card p n hn.ne']
    have hgen : Subgroup.zpowers g = ⊤ := by
      have := @Fintype.card_zpowers (GaloisField p n)ˣ _ _ g
      rw [hord_u] at this; apply Subgroup.eq_top_of_card_eq
      rw [← Fintype.card_eq_nat_card, ← Fintype.card_eq_nat_card]; exact this
    obtain ⟨k, hk⟩ := show Units.mk0 x hx ∈ Subgroup.zpowers g by rw [hgen]; trivial
    have : x = α ^ k := by
      have h := congr_arg Units.val hk
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at h; exact h.symm
    rw [this]
    exact zpow_mem (mem_adjoin_simple_self (ZMod p) (E := GaloisField p n) α) k

/-- If `g` is a generator of `(𝔽_{p^n})ˣ`, then its minimal polynomial over
`𝔽_p` is a primitive polynomial of degree `n` (cf. Theorem 3.15). -/
lemma generator_minpoly_is_prim (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 0 < n)
    (g : (GaloisField p n)ˣ) (hg : orderOf g = p ^ n - 1) :
    let f := minpoly (ZMod p) (g : GaloisField p n)
    f.IsPrimitivePolynomial p ∧ f.natDegree = n := by
  classical
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  set α := (g : GaloisField p n); set f := minpoly (ZMod p) α
  have hint : IsIntegral (ZMod p) α := Algebra.IsIntegral.isIntegral α
  have htop := adjoin_top_of_unit_generator p n hn g hg
  have hord_α : orderOf α = p ^ n - 1 := by
    change orderOf ((Units.coeHom _) g) = _
    rw [orderOf_injective (Units.coeHom _) Units.val_injective g, hg]
  have hf_deg : f.natDegree = n := by
    have h1 := adjoin.finrank hint
    have h2 : Module.finrank (ZMod p) ↥(ZMod p)⟮α⟯ = n := by
      rw [htop,
        (IntermediateField.topEquiv (F := ZMod p)
          (E := GaloisField p n)).toLinearEquiv.finrank_eq]
      exact GaloisField.finrank p hn.ne'
    linarith
  refine ⟨⟨minpoly.monic hint, minpoly.irreducible hint, ?_⟩, hf_deg⟩
  rw [hf_deg, orderOf_adjoinRoot_root_eq_orderOf (ZMod p) (GaloisField p n) α hint, hord_α]

end Theorem_3_15
