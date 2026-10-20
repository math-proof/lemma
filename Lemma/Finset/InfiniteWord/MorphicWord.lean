import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.InfiniteWord.MorphicWord
open MetaMathlibExt


/--
[IsMorphic.intro](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/MorphicWord.lean)
-/
@[path]
private lemma IsMorphic_intro_eq
  [Finite A]
  {u : Nat → A}
  {coding : A → B}
  {w : Nat → B}
-- given
  (hPure : IsPureMorphic u)
  (hCode : ∀ n, w n = coding (u n)) :
-- imply
  IsMorphic u coding w := by
-- proof
  apply MetaMathlibExt.IsMorphic.intro hPure hCode

/--
[IsMorphic.pure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/MorphicWord.lean)
-/
@[path]
private lemma IsMorphic_pure_eq
  [Finite A]
  {u : Nat → A}
  {coding : A → B}
  {w : Nat → B}
-- given
  (h : IsMorphic u coding w) :
-- imply
  IsPureMorphic u := by
-- proof
  apply MetaMathlibExt.IsMorphic.pure h

/--
[IsMorphic.coding_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/MorphicWord.lean)
-/
@[path]
private lemma IsMorphic_coding_eq_eq
  [Finite A]
  {u : Nat → A}
  {coding : A → B}
  {w : Nat → B}
  {n : Nat}
-- given
  (h : IsMorphic u coding w) :
-- imply
  w n = coding (u n) := by
-- proof
  apply MetaMathlibExt.IsMorphic.coding_eq h n

/--
[IsMorphic.ofPureMorphic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/MorphicWord.lean)
-/
@[path]
private lemma IsMorphic_ofPureMorphic_eq
  [Finite A]
  {u : Nat → A}
-- given
  (hu : IsPureMorphic u) :
-- imply
  IsMorphic u id u := by
-- proof
  apply MetaMathlibExt.IsMorphic.ofPureMorphic hu


-- created on 2026-10-20
