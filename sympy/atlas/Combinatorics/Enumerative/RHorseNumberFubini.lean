/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Rat.Defs
import sympy.atlas.Combinatorics.Enumerative.FubiniNumber
import Lemma.Finset.Enumerative.FubiniNumber
import Lemma.Finset.Enumerative.StirlingMatrices
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import sympy.atlas.Combinatorics.Enumerative.StirlingMatrices
/-! # r-horse numbers via Stirling-weighted Fubini values

This file proves the formula for `r`-horse numbers as a signed first-kind Stirling transform of
Fubini numbers.
-/

namespace MetaMathlibExt

open scoped BigOperators

private def rHorse_finSplit {n r : ℕ} (hrn : r ≤ n) :
    Fin r ⊕ Fin (n - r) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hrn))

private theorem rHorse_finSplit_inl {n r : ℕ} (hrn : r ≤ n) (i : Fin r) :
    rHorse_finSplit hrn (Sum.inl i) = Fin.castLE hrn i := by
  apply Fin.ext
  rfl

private def rHorse_functionSplit {n r : ℕ} (hrn : r ≤ n) (k : ℕ) :
    (Fin n → Fin k) ≃ (Fin r → Fin k) × (Fin (n - r) → Fin k) :=
  (Equiv.arrowCongr (rHorse_finSplit hrn) (Equiv.refl (Fin k))).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin r) (Fin (n - r)) (Fin k))

private theorem rHorse_functionSplit_fst {n r : ℕ} (hrn : r ≤ n) (k : ℕ)
    (f : Fin n → Fin k) (i : Fin r) :
    (rHorse_functionSplit hrn k f).1 i = f (Fin.castLE hrn i) := by
  simp [rHorse_functionSplit, rHorse_finSplit_inl]

private def rHorse_strictMonoEquivFinset (r k : ℕ) :
    { f : Fin r → Fin k // StrictMono f } ≃
      { s : Finset (Fin k) // s.card = r } where
  toFun f := ⟨Finset.image f.1 Finset.univ, by
    rw [Finset.card_image_of_injective _ f.property.injective, Finset.card_univ,
      Fintype.card_fin]⟩
  invFun s := ⟨s.1.orderEmbOfFin s.2, (s.1.orderEmbOfFin s.2).strictMono⟩
  left_inv f := by
    apply Subtype.ext
    symm
    apply Finset.orderEmbOfFin_unique
    · intro i
      simp
    · exact f.property
  right_inv s := by
    apply Subtype.ext
    exact Finset.image_orderEmbOfFin_univ s.1 s.2

private abbrev rHorseIncreasing {n r k : ℕ} (hrn : r ≤ n) (f : Fin n → Fin k) : Prop :=
  ∀ i j : Fin r, i < j → f (Fin.castLE hrn i) < f (Fin.castLE hrn j)

private abbrev rHorseSurjectiveIncreasing {n r k : ℕ} (hrn : r ≤ n)
    (f : Fin n → Fin k) : Prop :=
  Function.Surjective f ∧ rHorseIncreasing hrn f

private def rHorse_conditionEquiv {n r : ℕ} (hrn : r ≤ n) (k : ℕ) :
    { f : Fin n → Fin k // rHorseIncreasing hrn f } ≃
      { p : (Fin r → Fin k) × (Fin (n - r) → Fin k) // StrictMono p.1 } :=
  Equiv.subtypeEquiv (rHorse_functionSplit hrn k) fun f => by
    constructor
    · intro h i j hij
      simpa only [rHorse_functionSplit_fst] using h i j hij
    · intro h i j hij
      simpa only [rHorse_functionSplit_fst] using h hij

private def rHorse_conditionProdEquiv (n r k : ℕ) :
    { p : (Fin r → Fin k) × (Fin (n - r) → Fin k) // StrictMono p.1 } ≃
      { f : Fin r → Fin k // StrictMono f } × (Fin (n - r) → Fin k) where
  toFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv _p := rfl
  right_inv _p := rfl

private def rHorse_imageFiberEquiv {n r k : ℕ} (hrn : r ≤ n) (s : Finset (Fin k)) :
    { g : { g : Fin n → Fin k // rHorseIncreasing hrn g } //
        Finset.image g.1 Finset.univ = s } ≃
      { f : Fin n → Fin s.card // rHorseSurjectiveIncreasing hrn f } where
  toFun g := ⟨fun x => (s.orderIsoOfFin rfl).symm ⟨g.1.1 x, by
      have hx : g.1.1 x ∈ Finset.image g.1.1 Finset.univ :=
        Finset.mem_image_of_mem g.1.1 (Finset.mem_univ x)
      simpa only [← g.2] using hx⟩, by
    constructor
    · intro y
      have hy : ((s.orderIsoOfFin rfl y : s) : Fin k) ∈
          Finset.image g.1.1 Finset.univ := by
        rw [g.2]
        exact (s.orderIsoOfFin rfl y).property
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hy
      refine ⟨x, ?_⟩
      apply (s.orderIsoOfFin rfl).injective
      rw [OrderIso.apply_symm_apply]
      exact Subtype.ext hx
    · intro i j hij
      apply (s.orderIsoOfFin rfl).symm.lt_iff_lt.mpr
      exact g.1.2 i j hij⟩
  invFun f := ⟨⟨fun x => s.orderEmbOfFin rfl (f.1 x), by
      intro i j hij
      exact (s.orderEmbOfFin rfl).strictMono (f.2.2 i j hij)⟩, by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      exact Finset.orderEmbOfFin_mem s rfl (f.1 x)
    · intro hz
      obtain ⟨x, hx⟩ := f.2.1 ((s.orderIsoOfFin rfl).symm ⟨z, hz⟩)
      refine ⟨x, ?_⟩
      rw [hx, ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    simp only
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  right_inv f := by
    apply Subtype.ext
    funext x
    apply (s.orderIsoOfFin rfl).injective
    rw [OrderIso.apply_symm_apply]
    exact Subtype.ext (Finset.coe_orderIsoOfFin_apply s rfl (f.1 x)).symm

private def rHorseCandidate (n r i : ℕ) : ℚ :=
  (1 / (Nat.factorial r : ℚ)) *
    ∑ j ∈ Finset.range (r + 1),
      (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
        ((Nat.factorial i : ℚ) * (Nat.stirlingSecond (n - j) i : ℚ))
end MetaMathlibExt
