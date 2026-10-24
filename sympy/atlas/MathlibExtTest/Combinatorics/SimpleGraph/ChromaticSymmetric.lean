/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/ChromaticSymmetric.lean -/


import sympy.atlas.Combinatorics.SimpleGraph.ChromaticSymmetric
import Lemma.SimpleGraph.ChromaticSymmetric


namespace SimpleGraph

example {V : Type*} [Finite V] (G : SimpleGraph V) : SameChromaticSymmetricFunction G G :=
  SameChromaticSymmetricFunction.refl G

example {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (h : SameChromaticSymmetricFunction G H) : SameChromaticSymmetricFunction H G :=
  h.symm

example {V W U : Type*} [Finite V] [Finite W] [Finite U]
    {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph U}
    (hGH : SameChromaticSymmetricFunction G H)
    (hHK : SameChromaticSymmetricFunction H K) : SameChromaticSymmetricFunction G K :=
  hGH.trans hHK

example {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    SameChromaticSymmetricFunction G H :=
  SameChromaticSymmetricFunction.of_iso e

/-- Semantic test: the edgeless graph on one vertex admits exactly one proper
coloring with the single available color used once, so this profile count is
`1`; a constant-zero count function would fail this test. -/
example : chromaticProfileCount (⊥ : SimpleGraph (Fin 1)) 1 (fun _ => 1) = 1 := by
  classical
  unfold chromaticProfileCount
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨Coloring.mk (fun _ => 0) (fun h => ((bot_adj _ _).mp h).elim), ?_⟩, ?_⟩
  · intro color
    fin_cases color
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨⟨0, rfl⟩, fun x => Subtype.ext (Fin.eq_zero x.1)⟩
  · rintro ⟨c, -⟩
    apply Subtype.ext
    apply DFunLike.ext
    intro v
    exact Subsingleton.elim _ _

/-- Semantic test: a single edge cannot be properly colored with one color
used twice, so this profile count is `0`. -/
example : chromaticProfileCount (completeGraph (Fin 2)) 1 (fun _ => 2) = 0 := by
  classical
  unfold chromaticProfileCount
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨c, -⟩
  exact c.valid (show (completeGraph (Fin 2)).Adj 0 1 by decide) (Subsingleton.elim _ _)

end SimpleGraph
