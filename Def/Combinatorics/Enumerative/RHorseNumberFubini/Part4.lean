/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Rat.Defs
import Def.Combinatorics.Enumerative.FubiniNumber
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
import Def.Combinatorics.Enumerative.StirlingMatrices
import Abbrev.Combinatorics.Enumerative.RHorseNumberFubini
/-! # r-horse numbers via Stirling-weighted Fubini values

This file proves the formula for `r`-horse numbers as a signed first-kind Stirling transform of
Fubini numbers.
-/


namespace MetaMathlibExt

open scoped BigOperators

def rHorse_conditionEquiv {n r : ℕ} (hrn : r ≤ n) (k : ℕ) :
    { f : Fin n → Fin k // rHorseIncreasing hrn f } ≃
      { p : (Fin r → Fin k) × (Fin (n - r) → Fin k) // StrictMono p.1 } :=
  Equiv.subtypeEquiv (rHorse_functionSplit hrn k) fun f => by
    constructor
    · intro h i j hij
      simpa only [rHorse_functionSplit_fst] using h i j hij
    · intro h i j hij
      simpa only [rHorse_functionSplit_fst] using h hij

def rHorse_conditionProdEquiv (n r k : ℕ) :
    { p : (Fin r → Fin k) × (Fin (n - r) → Fin k) // StrictMono p.1 } ≃
      { f : Fin r → Fin k // StrictMono f } × (Fin (n - r) → Fin k) where
  toFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv _p := rfl
  right_inv _p := rfl

def rHorse_imageFiberEquiv {n r k : ℕ} (hrn : r ≤ n) (s : Finset (Fin k)) :
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

def rHorseCandidate (n r i : ℕ) : ℚ :=
  (1 / (Nat.factorial r : ℚ)) *
    ∑ j ∈ Finset.range (r + 1),
      (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
        ((Nat.factorial i : ℚ) * (Nat.stirlingSecond (n - j) i : ℚ))

end MetaMathlibExt
