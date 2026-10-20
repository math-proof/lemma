/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Logic/GodelRosserAbstractSchema.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Nat.Basic

/-!
# Abstract Gödel-Rosser incompleteness schema

This file derives a true undecidable closed sentence from abstract proof coding,
Rosser representability, consistency, and a diagonal fixed-point interface.
-/

namespace MetaMathlibExt

private theorem rosser_rProvable_implies_provable
    {Sentence : Type} {neg : Sentence → Sentence}
    {Provable RProvable : Sentence → Prop} {Proof : Sentence → ℕ → Prop}
    (hProof : ∀ s, Provable s ↔ ∃ n, Proof s n)
    (hRProof : ∀ s, RProvable s ↔ ∃ n, Proof s n ∧ ∀ m, m < n → ¬ Proof (neg s) m)
    {s : Sentence} (hs : RProvable s) : Provable s := by
  obtain ⟨n, hn, _⟩ := (hRProof s).mp hs
  exact (hProof s).mpr ⟨n, hn⟩

private theorem rosser_not_provable
    {Sentence : Type} {neg : Sentence → Sentence} {imp : Sentence → Sentence → Sentence}
    {subst : Sentence → ℕ → Sentence} {Provable RProvable : Sentence → Prop}
    {Proof : Sentence → ℕ → Prop} {rPr : Sentence} {code : Sentence → ℕ}
    (hMp : ∀ A B, Provable (imp A B) → Provable A → Provable B)
    (hConsistent : ∀ A, Provable A → Provable (neg A) → False)
    (hProof : ∀ s, Provable s ↔ ∃ n, Proof s n)
    (hRProof : ∀ s, RProvable s ↔ ∃ n, Proof s n ∧ ∀ m, m < n → ¬ Proof (neg s) m)
    (hRProvableComplete : ∀ s, RProvable s → Provable (subst rPr (code s)))
    {G : Sentence} (hDiagonalForward : Provable (imp G (neg (subst rPr (code G))))) :
    ¬ Provable G := by
  intro hG
  obtain ⟨n, hn⟩ := (hProof G).mp hG
  have hNoShortRefutation : ∀ m, m < n → ¬ Proof (neg G) m := by
    intro m _ hm
    have hnegG : Provable (neg G) := (hProof (neg G)).mpr ⟨m, hm⟩
    exact hConsistent G hG hnegG
  have hRG : RProvable G :=
    (hRProof G).mpr ⟨n, hn, hNoShortRefutation⟩
  have hRPr : Provable (subst rPr (code G)) := hRProvableComplete G hRG
  have hnotRPr : Provable (neg (subst rPr (code G))) :=
    hMp G (neg (subst rPr (code G))) hDiagonalForward hG
  exact hConsistent (subst rPr (code G)) hRPr hnotRPr

private theorem rosser_not_refutable
    {Sentence : Type} {neg : Sentence → Sentence} {imp : Sentence → Sentence → Sentence}
    {subst : Sentence → ℕ → Sentence} {Provable : Sentence → Prop}
    {rPr : Sentence} {code : Sentence → ℕ}
    (hMp : ∀ A B, Provable (imp A B) → Provable A → Provable B)
    (hConsistent : ∀ A, Provable A → Provable (neg A) → False)
    (hRefutationTransfer : ∀ s, Provable (neg s) → Provable (neg (subst rPr (code s))))
    {G : Sentence}
    (hDiagonalBackward : Provable (imp (neg (subst rPr (code G))) G)) :
    ¬ Provable (neg G) := by
  intro hnegG
  have hnegRPr : Provable (neg (subst rPr (code G))) :=
    hRefutationTransfer G hnegG
  have hG : Provable G :=
    hMp (neg (subst rPr (code G))) G hDiagonalBackward hnegRPr
  exact hConsistent G hG hnegG

private theorem rosser_true
    {Sentence : Type} {neg : Sentence → Sentence} {subst : Sentence → ℕ → Sentence}
    {Provable RProvable TrueInN : Sentence → Prop} {Proof : Sentence → ℕ → Prop}
    {rPr : Sentence} {code : Sentence → ℕ}
    (hTrueNeg : ∀ A, TrueInN (neg A) ↔ ¬ TrueInN A)
    (hProof : ∀ s, Provable s ↔ ∃ n, Proof s n)
    (hRProof : ∀ s, RProvable s ↔ ∃ n, Proof s n ∧ ∀ m, m < n → ¬ Proof (neg s) m)
    (hRPrTruth : ∀ s, TrueInN (subst rPr (code s)) ↔ RProvable s)
    {G : Sentence}
    (hDiagonalTruth : TrueInN G ↔ TrueInN (neg (subst rPr (code G))))
    (hNotProvable : ¬ Provable G) : TrueInN G := by
  have hNotRProvable : ¬ RProvable G := by
    intro hRG
    exact hNotProvable (rosser_rProvable_implies_provable hProof hRProof hRG)
  have hNotRPrTrue : ¬ TrueInN (subst rPr (code G)) := by
    intro hRPrTrue
    exact hNotRProvable ((hRPrTruth G).mp hRPrTrue)
  have hNegRPrTrue : TrueInN (neg (subst rPr (code G))) :=
    (hTrueNeg (subst rPr (code G))).mpr hNotRPrTrue
  exact hDiagonalTruth.mpr hNegRPrTrue

/-- Abstract Rosser schema: sentence-level proof coding, truth, positive Rosser representability,
a proof-triggered negative representability principle, and a diagonal fixed-point interface yield
a true sentence that is neither provable nor refutable. This deliberately does not claim to derive
those interfaces from a concrete effective arithmetic syntax.

Sources: Kurt Gödel, *Über formal unentscheidbare Sätze der Principia Mathematica und
verwandter Systeme I*, Monatshefte für Mathematik und Physik 38 (1931), 173–198;
J. Barkley Rosser, *Extensions of some theorems of Gödel and Church*, Journal of
Symbolic Logic 1 (1936), 87–91.

Proves `Wanted` entry `godel_rosser_abstract_schema`.

Proof: Apply diagonalization to the negation of the Rosser provability formula, then use
consistency and representability as in Rosser (1936) and Smith, 2nd ed., Chapter 25.
-/
theorem godel_rosser_abstract_schema :
    ∀ (Sentence : Type)
      (neg : Sentence → Sentence) (imp : Sentence → Sentence → Sentence)
      (subst : Sentence → ℕ → Sentence)
      (Provable RProvable TrueInN : Sentence → Prop)
      (Proof : Sentence → ℕ → Prop) (rPr : Sentence) (code : Sentence → ℕ),
      (∀ G, TrueInN (neg G) ↔ ¬ TrueInN G) →
      (∀ A B, Provable (imp A B) → Provable A → Provable B) →
      (∀ A, Provable A → Provable (neg A) → False) →
      (∀ A n, subst (neg A) n = neg (subst A n)) →
      (∀ s, Provable s ↔ ∃ n, Proof s n) →
      (∀ s, RProvable s ↔ ∃ n, Proof s n ∧ ∀ m, m < n → ¬ Proof (neg s) m) →
      (∀ s, TrueInN (subst rPr (code s)) ↔ RProvable s) →
      (∀ s, RProvable s → Provable (subst rPr (code s))) →
      (∀ s, Provable (neg s) → Provable (neg (subst rPr (code s)))) →
      (∀ F, ∃ G, (∀ n, subst G n = G) ∧
        Provable (imp G (subst F (code G))) ∧
        Provable (imp (subst F (code G)) G) ∧
        (TrueInN G ↔ TrueInN (subst F (code G)))) →
      ∃ G : Sentence, (∀ n, subst G n = G) ∧
        TrueInN G ∧ ¬ Provable G ∧ ¬ Provable (neg G) := by
  intro Sentence neg imp subst Provable RProvable TrueInN Proof rPr code hTrueNeg hMp
    hConsistent hSubstNeg hProof hRProof hRPrTruth hRProvableComplete hRefutationTransfer
    hDiagonal
  obtain ⟨G, hClosed, hDiagonalForward, hDiagonalBackward, hDiagonalTruth⟩ :=
    hDiagonal (neg rPr)
  rw [hSubstNeg rPr (code G)] at hDiagonalForward hDiagonalBackward hDiagonalTruth
  have hNotProvable : ¬ Provable G :=
    rosser_not_provable hMp hConsistent hProof hRProof hRProvableComplete hDiagonalForward
  have hNotRefutable : ¬ Provable (neg G) :=
    rosser_not_refutable hMp hConsistent hRefutationTransfer hDiagonalBackward
  have hTrue : TrueInN G :=
    rosser_true hTrueNeg hProof hRProof hRPrTruth hDiagonalTruth hNotProvable
  exact ⟨G, hClosed, hTrue, hNotProvable, hNotRefutable⟩

end MetaMathlibExt
