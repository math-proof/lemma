/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Logic/GodelRosserAbstractSchema.lean -/


import Lemma.Set.GodelRosserAbstractSchema
open MetaMathlibExt


-- The public theorem produces an undecidable truth from the abstract Rosser hypotheses.
example
    (Sentence : Type)
    (neg : Sentence → Sentence) (imp : Sentence → Sentence → Sentence)
    (subst : Sentence → ℕ → Sentence)
    (Provable RProvable TrueInN : Sentence → Prop)
    (Proof : Sentence → ℕ → Prop) (rPr : Sentence) (code : Sentence → ℕ)
    (hTrueNeg : ∀ G, TrueInN (neg G) ↔ ¬ TrueInN G)
    (hMp : ∀ A B, Provable (imp A B) → Provable A → Provable B)
    (hConsistent : ∀ A, Provable A → Provable (neg A) → False)
    (hSubstNeg : ∀ A n, subst (neg A) n = neg (subst A n))
    (hProof : ∀ s, Provable s ↔ ∃ n, Proof s n)
    (hRProof : ∀ s, RProvable s ↔ ∃ n, Proof s n ∧ ∀ m, m < n → ¬ Proof (neg s) m)
    (hRPrTruth : ∀ s, TrueInN (subst rPr (code s)) ↔ RProvable s)
    (hRProvableComplete : ∀ s, RProvable s → Provable (subst rPr (code s)))
    (hRefutationTransfer : ∀ s, Provable (neg s) → Provable (neg (subst rPr (code s))))
    (hDiagonal : ∀ F, ∃ G, (∀ n, subst G n = G) ∧
      Provable (imp G (subst F (code G))) ∧
      Provable (imp (subst F (code G)) G) ∧
      (TrueInN G ↔ TrueInN (subst F (code G)))) :
    ∃ G : Sentence, (∀ n, subst G n = G) ∧
      TrueInN G ∧ ¬ Provable G ∧ ¬ Provable (neg G) :=
  godel_rosser_abstract_schema Sentence neg imp subst Provable RProvable TrueInN Proof rPr code
    hTrueNeg hMp hConsistent hSubstNeg hProof hRProof hRPrTruth hRProvableComplete
    hRefutationTransfer hDiagonal

