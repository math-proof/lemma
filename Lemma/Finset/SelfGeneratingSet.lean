import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SelfGeneratingSet
open MetaMathlibExt
open SelfGeneratingSet


/--
[fixedPoint_isSG](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
private lemma fixedPoint_isSG_eq
  {F : Finset (Nat → Nat)}
  {seed : Nat}
  {C : Set Nat}
-- given
  (hC : FixedPoint F seed C) :
-- imply
  SG F seed C := by
-- proof
  apply MetaMathlibExt.SelfGeneratingSet.fixedPoint_isSG hC

/--
[generated_isSG](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
private lemma generated_isSG_eq
  {F : Finset (Nat → Nat)}
  {seed : Nat} :
-- imply
  SG F seed (GeneratedSet F seed) := by
-- proof
  apply MetaMathlibExt.SelfGeneratingSet.generated_isSG

/--
[generated_le_of_sg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
private lemma generated_le_of_sg_eq
  {F : Finset (Nat → Nat)}
  {seed : Nat}
  {G : Set Nat}
-- given
  (hG : SG F seed G) :
-- imply
  GeneratedSet F seed ⊆ G := by
-- proof
  apply MetaMathlibExt.SelfGeneratingSet.generated_le_of_sg hG

/--
[generated_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
private lemma generated_fixedPoint_eq
  {F : Finset (Nat → Nat)}
  {seed : Nat} :
-- imply
  FixedPoint F seed (GeneratedSet F seed) := by
-- proof
  apply MetaMathlibExt.SelfGeneratingSet.generated_fixedPoint

/--
[fixedPoint_eq_generated](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
private lemma fixedPoint_eq_generated_eq
  {F : Finset (Nat → Nat)}
  {seed : Nat}
  {C : Set Nat}
-- given
  (hg : StrictGrowth F)
  (hC : FixedPoint F seed C) :
-- imply
  C = GeneratedSet F seed := by
-- proof
  apply MetaMathlibExt.SelfGeneratingSet.fixedPoint_eq_generated hg hC

/--
[generated_eq_sInter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
private lemma generated_eq_sInter_eq
  {F : Finset (Nat → Nat)}
  {seed : Nat} :
-- imply
  GeneratedSet F seed = Set.sInter {G | SG F seed G} := by
-- proof
  apply MetaMathlibExt.SelfGeneratingSet.generated_eq_sInter

/--
[fixedPoint_eq_sInter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
private lemma fixedPoint_eq_sInter_eq
  {F : Finset (Nat → Nat)}
  {seed : Nat}
  {C : Set Nat}
-- given
  (hg : StrictGrowth F)
  (hC : FixedPoint F seed C) :
-- imply
  C = Set.sInter {G | SG F seed G} := by
-- proof
  apply MetaMathlibExt.SelfGeneratingSet.fixedPoint_eq_sInter hg hC

/--
[fixedPoint_isLeast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
private lemma fixedPoint_isLeast_eq
  {F : Finset (Nat → Nat)}
  {seed : Nat}
  {C : Set Nat}
-- given
  (hg : StrictGrowth F)
  (hC : FixedPoint F seed C) :
-- imply
  SG F seed C ∧ ∀ G, SG F seed G → C ⊆ G := by
-- proof
  apply MetaMathlibExt.SelfGeneratingSet.fixedPoint_isLeast hg hC

/--
[isLeast_eq_generated](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
private lemma isLeast_eq_generated_eq
  {F : Finset (Nat → Nat)}
  {seed : Nat}
  {C : Set Nat}
-- given
  (hC : SG F seed C)
  (hle : ∀ G, SG F seed G → C ⊆ G) :
-- imply
  C = GeneratedSet F seed := by
-- proof
  apply MetaMathlibExt.SelfGeneratingSet.isLeast_eq_generated hC hle

/--
[fixedPoint_unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
private lemma fixedPoint_unique_eq
  {F : Finset (Nat → Nat)}
  {seed : Nat}
  {C1 C2 : Set Nat}
-- given
  (hg : StrictGrowth F)
  (h0 : FixedPoint F seed C1)
  (h1 : FixedPoint F seed C2) :
-- imply
  C1 = C2 := by
-- proof
  apply MetaMathlibExt.SelfGeneratingSet.fixedPoint_unique hg h0 h1


-- created on 2026-10-20
