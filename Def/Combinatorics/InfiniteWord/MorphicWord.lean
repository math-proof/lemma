/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/MorphicWord.lean -/

import Def.Combinatorics.InfiniteWord.PureMorphicWord
import Lemma.Finset.InfiniteWord.PureMorphicWord


namespace MetaMathlibExt

/-- A morphic word is the normalized coding image of a pure morphic word.

Concept `jis_sem_8aa01797a09c6951299c4a2d`; source statements
`jis_305f669a0778b2b0011670ec`, `jis_59581da9ed7395999b79fb6c`,
`jis_d868c1fc64073e778b524189`, and `jis_de6cb6fe1f9e977bace8a77d`. -/
def IsMorphic {A B : Type*} [Finite A] (u : Nat → A) (coding : A → B) (w : Nat → B) : Prop :=
  IsPureMorphic u ∧ ∀ n, w n = coding (u n)

end MetaMathlibExt
