import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.InfiniteWord.MorphicWord
open MetaMathlibExt


namespace MetaMathlibExt

/--
[IsMorphic.intro](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/MorphicWord.lean)
-/
@[path]
lemma IsMorphic.intro
  [Finite A]
  {u : Nat → A}
  {coding : A → B}
  {w : Nat → B}
-- given
  (hPure : IsPureMorphic u)
  (hCode : ∀ n, w n = coding (u n)) :
-- imply
  IsMorphic u coding w :=
-- proof
  ⟨hPure, hCode⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsMorphic.pure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/MorphicWord.lean)
-/
@[path]
lemma IsMorphic.pure
  [Finite A]
  {u : Nat → A}
  {coding : A → B}
  {w : Nat → B}
-- given
  (h : IsMorphic u coding w) :
-- imply
  IsPureMorphic u :=
-- proof
  h.1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsMorphic.coding_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/MorphicWord.lean)
-/
@[path]
lemma IsMorphic.coding_eq
  [Finite A]
  {u : Nat → A}
  {coding : A → B}
  {w : Nat → B}
  {n : Nat}
-- given
  (h : IsMorphic u coding w) :
-- imply
  w n = coding (u n) :=
-- proof
  h.2 n

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsMorphic.ofPureMorphic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/MorphicWord.lean)
-/
@[path]
lemma IsMorphic.ofPureMorphic
  [Finite A]
  {u : Nat → A}
-- given
  (hu : IsPureMorphic u) :
-- imply
  IsMorphic u id u :=
-- proof
  ⟨hu, fun _ => rfl⟩

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
