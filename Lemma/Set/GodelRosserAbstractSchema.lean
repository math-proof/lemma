import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[rosser_rProvable_implies_provable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Logic/GodelRosserAbstractSchema.lean)
-/
@[path]
private lemma rosser_rProvable_implies_provable
  {Sentence : Type} {neg : Sentence → Sentence}
  {Provable RProvable : Sentence → Prop} {Proof : Sentence → ℕ → Prop}
  (hProof : ∀ s, Provable s ↔ ∃ n, Proof s n)
  (hRProof : ∀ s, RProvable s ↔ ∃ n, Proof s n ∧ ∀ m, m < n → ¬ Proof (neg s) m)
  {s : Sentence} (hs : RProvable s) : Provable s := by
  obtain ⟨n, hn, _⟩ := (hRProof s).mp hs
  exact (hProof s).mpr ⟨n, hn⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rosser_not_provable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Logic/GodelRosserAbstractSchema.lean)
-/
@[path]
private lemma rosser_not_provable
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

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rosser_not_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Logic/GodelRosserAbstractSchema.lean)
-/
@[path]
private lemma rosser_not_refutable
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

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rosser_true](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Logic/GodelRosserAbstractSchema.lean)
-/
@[path]
private lemma rosser_true
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

end MetaMathlibExt

namespace MetaMathlibExt

/--
[godel_rosser_abstract_schema](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Logic/GodelRosserAbstractSchema.lean)
-/
@[path]
lemma godel_rosser_abstract_schema
  :
-- imply
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
-- proof
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


-- created on 2026-10-20
-- updated on 2026-10-26
