/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/CommonDifferenceProgressions.lean -/

import Def.Combinatorics.AP.Basic.Part2
import Lemma.Set.APBasic


namespace MetaMathlibExt

/-- Common-difference progressions: holds exactly when there is one shared
`d : G` such that `A` and `B` are both set-level arithmetic progressions of
their own cardinalities with difference `d`, stated directly with
`Set.IsAPOfLengthWith`; the two progressions may have different initial
terms and different cardinalities.

Source: Fabián Arias, Jerson Borja, and Samuel Anaya, *Counting Integers
Representable as Sums of k-th Powers Modulo n*, Journal of Integer Sequences
26 (2023), Article 23.8.1, Theorem [Vosper] `theo_Vosper` condition (iii),
lines 256–267,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Borja/borja4.tex>:
"`A` and `B` are arithmetic progressions with the same common difference". -/
def AreFiniteArithmeticProgressionsWithCommonDifference {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (A B : Finset G) : Prop :=
  ∃ d a b : G, (A : Set G).IsAPOfLengthWith A.card a d ∧
    (B : Set G).IsAPOfLengthWith B.card b d

end MetaMathlibExt
