/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Logic/HilbertBernaysLob.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Init

/-!
# Gödel's second incompleteness theorem

This file derives the second incompleteness theorem from an abstract Hilbert system and
the Hilbert–Bernays–Löb derivability conditions.
-/

namespace MetaMathlibExt

private theorem hbl_compose
    {Sentence : Type} (Proves : (Sentence → Prop) → Sentence → Prop)
    (imp : Sentence → Sentence → Sentence)
    (mp : ∀ (U : Sentence → Prop) (a b : Sentence),
      Proves U (imp a b) → Proves U a → Proves U b)
    (k : ∀ (U : Sentence → Prop) (a b : Sentence), Proves U (imp a (imp b a)))
    (s : ∀ (U : Sentence → Prop) (a b c : Sentence),
      Proves U (imp (imp a (imp b c)) (imp (imp a b) (imp a c))))
    (U : Sentence → Prop) (a b c : Sentence)
    (hab : Proves U (imp a b)) (hbc : Proves U (imp b c)) :
    Proves U (imp a c) := by
  have habc : Proves U (imp a (imp b c)) :=
    mp U (imp b c) (imp a (imp b c)) (k U (imp b c) a) hbc
  exact mp U (imp a b) (imp a c)
    (mp U (imp a (imp b c)) (imp (imp a b) (imp a c)) (s U a b c) habc) hab

private theorem hbl_apply_under
    {Sentence : Type} (Proves : (Sentence → Prop) → Sentence → Prop)
    (imp : Sentence → Sentence → Sentence)
    (mp : ∀ (U : Sentence → Prop) (a b : Sentence),
      Proves U (imp a b) → Proves U a → Proves U b)
    (s : ∀ (U : Sentence → Prop) (a b c : Sentence),
      Proves U (imp (imp a (imp b c)) (imp (imp a b) (imp a c))))
    (U : Sentence → Prop) (a b c : Sentence)
    (habc : Proves U (imp a (imp b c))) (hab : Proves U (imp a b)) :
    Proves U (imp a c) := by
  exact mp U (imp a b) (imp a c)
    (mp U (imp a (imp b c)) (imp (imp a b) (imp a c)) (s U a b c) habc) hab

private theorem hbl_contraposition
    {Sentence : Type} (Proves : (Sentence → Prop) → Sentence → Prop)
    (imp : Sentence → Sentence → Sentence)
    (mp : ∀ (U : Sentence → Prop) (a b : Sentence),
      Proves U (imp a b) → Proves U a → Proves U b)
    (k : ∀ (U : Sentence → Prop) (a b : Sentence), Proves U (imp a (imp b a)))
    (s : ∀ (U : Sentence → Prop) (a b c : Sentence),
      Proves U (imp (imp a (imp b c)) (imp (imp a b) (imp a c))))
    (U : Sentence → Prop) (falseStmt a b : Sentence) (hab : Proves U (imp a b)) :
    Proves U (imp (imp b falseStmt) (imp a falseStmt)) := by
  have hqaq : Proves U (imp (imp b falseStmt) (imp a (imp b falseStmt))) :=
    k U (imp b falseStmt) a
  have hqstep : Proves U (imp (imp b falseStmt) (imp (imp a b) (imp a falseStmt))) :=
    hbl_compose Proves imp mp k s U (imp b falseStmt) (imp a (imp b falseStmt))
      (imp (imp a b) (imp a falseStmt)) hqaq (s U a b falseStmt)
  have hqab : Proves U (imp (imp b falseStmt) (imp a b)) :=
    mp U (imp a b) (imp (imp b falseStmt) (imp a b))
      (k U (imp a b) (imp b falseStmt)) hab
  exact hbl_apply_under Proves imp mp s U (imp b falseStmt) (imp a b)
    (imp a falseStmt) hqstep hqab

private theorem hbl_prov_implies_prov_false
    {Sentence : Type} (Proves : (Sentence → Prop) → Sentence → Prop)
    (imp : Sentence → Sentence → Sentence) (Prov : Sentence → Sentence)
    (mp : ∀ (U : Sentence → Prop) (a b : Sentence),
      Proves U (imp a b) → Proves U a → Proves U b)
    (k : ∀ (U : Sentence → Prop) (a b : Sentence), Proves U (imp a (imp b a)))
    (s : ∀ (U : Sentence → Prop) (a b c : Sentence),
      Proves U (imp (imp a (imp b c)) (imp (imp a b) (imp a c))))
    (U : Sentence → Prop) (falseStmt G : Sentence)
    (d1 : ∀ t, Proves U t → Proves U (Prov t))
    (d2 : ∀ a b, Proves U (imp (Prov (imp a b)) (imp (Prov a) (Prov b))))
    (d3 : ∀ t, Proves U (imp (Prov t) (Prov (Prov t))))
    (hfixed : Proves U (imp G (imp (Prov G) falseStmt))) :
    Proves U (imp (Prov G) (Prov falseStmt)) := by
  have hboxed : Proves U (Prov (imp G (imp (Prov G) falseStmt))) :=
    d1 (imp G (imp (Prov G) falseStmt)) hfixed
  have hfirst : Proves U (imp (Prov G) (Prov (imp (Prov G) falseStmt))) :=
    mp U (Prov (imp G (imp (Prov G) falseStmt)))
      (imp (Prov G) (Prov (imp (Prov G) falseStmt)))
      (d2 G (imp (Prov G) falseStmt)) hboxed
  have hchain : Proves U
      (imp (Prov G) (imp (Prov (Prov G)) (Prov falseStmt))) :=
    hbl_compose Proves imp mp k s U (Prov G) (Prov (imp (Prov G) falseStmt))
      (imp (Prov (Prov G)) (Prov falseStmt)) hfirst (d2 (Prov G) falseStmt)
  exact hbl_apply_under Proves imp mp s U (Prov G) (Prov (Prov G))
    (Prov falseStmt) hchain (d3 G)

/-- Purely abstract Hilbert–Bernays–Löb derivability schema. A theory `T` has an
internal provability operator satisfying the derivability conditions, an internal fixed
point for its own unprovability, and a consistency sentence
`Con = neg (Prov falseStmt)`. If `T` is consistent, it does not prove `Con`.

This declaration assumes the derivability and fixed-point interface rather than deriving
it from a concrete encoding of first-order arithmetic.

Sources: Kurt Gödel, *Über formal unentscheidbare Sätze der Principia Mathematica und
verwandter Systeme I*, Monatshefte für Mathematik und Physik 38 (1931), 173–198;
Martin H. Löb, *Solution of a problem of Leon Henkin*, Journal of Symbolic Logic 20
(1955), 115–118.

Proves `Wanted` entry `hilbert_bernays_lob_second_incompleteness`.

Proof: Derive the needed implicational combinators from K and S, apply D1–D3 to the Gödel
fixed point, and contrapose `Prov G → Prov falseStmt`. This is the Hilbert–Bernays–Löb route
of Hilbert–Bernays (1939) and Löb (1955), as presented by Boolos, Ch. 3, and Smith, Ch. 33.
-/
theorem hilbert_bernays_lob_second_incompleteness :
    ∀ (Sentence : Type)
      (Proves : (Sentence → Prop) → Sentence → Prop) (T : Sentence → Prop)
      (Con falseStmt : Sentence) (neg Prov : Sentence → Sentence)
      (imp : Sentence → Sentence → Sentence) (BaseTheory : Sentence → Prop),
      (∀ s, Proves BaseTheory s → Proves T s) →
      (∀ (U : Sentence → Prop) (a b : Sentence),
        Proves U (imp a b) → Proves U a → Proves U b) →
      (∀ (U : Sentence → Prop) (a b : Sentence), Proves U (imp a (imp b a))) →
      (∀ (U : Sentence → Prop) (a b c : Sentence),
        Proves U (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))) →
      (∀ s, neg s = imp s falseStmt) →
      (∃ G, Proves BaseTheory (imp G (neg (Prov G))) ∧
        Proves BaseTheory (imp (neg (Prov G)) G)) →
      (∀ s, Proves T s → Proves T (Prov s)) →
      (∀ a b, Proves T (imp (Prov (imp a b)) (imp (Prov a) (Prov b)))) →
      (∀ s, Proves T (imp (Prov s) (Prov (Prov s)))) →
      (Con = neg (Prov falseStmt)) →
      ¬ Proves T falseStmt →
      ¬ Proves T Con := by
  intro Sentence Proves T Con falseStmt neg Prov imp BaseTheory base mp k s neg_eq diagonal d1 d2
    d3 con_eq consistent hcon
  obtain ⟨G, hGdiag, hdiagG⟩ := diagonal
  have hGneg : Proves T (imp G (imp (Prov G) falseStmt)) := by
    rw [← neg_eq (Prov G)]
    exact base (imp G (neg (Prov G))) hGdiag
  have hnegG : Proves T (imp (imp (Prov G) falseStmt) G) := by
    rw [← neg_eq (Prov G)]
    exact base (imp (neg (Prov G)) G) hdiagG
  have hprovFalse : Proves T (imp (Prov G) (Prov falseStmt)) :=
    hbl_prov_implies_prov_false Proves imp Prov mp k s T falseStmt G d1 d2 d3 hGneg
  have hcontra : Proves T
      (imp (imp (Prov falseStmt) falseStmt) (imp (Prov G) falseStmt)) :=
    hbl_contraposition Proves imp mp k s T falseStmt (Prov G) (Prov falseStmt) hprovFalse
  have hconG : Proves T (imp (imp (Prov falseStmt) falseStmt) G) :=
    hbl_compose Proves imp mp k s T (imp (Prov falseStmt) falseStmt)
      (imp (Prov G) falseStmt) G hcontra hnegG
  have hconImp : Proves T (imp (Prov falseStmt) falseStmt) := by
    rw [← neg_eq (Prov falseStmt), ← con_eq]
    exact hcon
  have hG : Proves T G :=
    mp T (imp (Prov falseStmt) falseStmt) G hconG hconImp
  have hprovG : Proves T (Prov G) := d1 G hG
  have hnotProvG : Proves T (imp (Prov G) falseStmt) :=
    mp T G (imp (Prov G) falseStmt) hGneg hG
  exact consistent (mp T (Prov G) falseStmt hnotProvG hprovG)

end MetaMathlibExt
