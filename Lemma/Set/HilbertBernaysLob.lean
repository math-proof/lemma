import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[hbl_compose](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Logic/HilbertBernaysLob.lean)
-/
@[path]
private lemma hbl_compose
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

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hbl_apply_under](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Logic/HilbertBernaysLob.lean)
-/
@[path]
private lemma hbl_apply_under
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

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hbl_contraposition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Logic/HilbertBernaysLob.lean)
-/
@[path]
private lemma hbl_contraposition
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

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hbl_prov_implies_prov_false](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Logic/HilbertBernaysLob.lean)
-/
@[path]
private lemma hbl_prov_implies_prov_false
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

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hilbert_bernays_lob_second_incompleteness](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Logic/HilbertBernaysLob.lean)
-/
@[path]
lemma hilbert_bernays_lob_second_incompleteness
  :
-- imply
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
-- proof
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
    rwa [← neg_eq (Prov falseStmt), ← con_eq]
  have hG : Proves T G :=
    mp T (imp (Prov falseStmt) falseStmt) G hconG hconImp
  have hprovG : Proves T (Prov G) := d1 G hG
  have hnotProvG : Proves T (imp (Prov G) falseStmt) :=
    mp T G (imp (Prov G) falseStmt) hGneg hG
  exact consistent (mp T (Prov G) falseStmt hnotProvG hprovG)

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
