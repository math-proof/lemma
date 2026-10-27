import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.VecPivotalConcrete.Part2
open CategoryTheory MonoidalCategory Module Category TensorCategories


/--
[vecDoubleDualIsoConcrete_naturality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecPivotalConcrete.lean)
-/
@[path]
private lemma vecDoubleDualIsoConcrete_naturality_eq
  {k : Type u}
  [Field k]
  {V W : FGModuleCat.{u} k}
  {f : V ⟶ W} :
-- imply
  f ≫ (vecDoubleDualIsoConcrete k W).hom = (vecDoubleDualIsoConcrete k V).hom ≫ (rightAdjointMate (rightAdjointMate f)) := by
-- proof
  apply vecDoubleDualIsoConcrete_naturality k f

/--
[vecDoubleDualIsoConcrete_monoidality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecPivotalConcrete.lean)
-/
@[path]
private lemma vecDoubleDualIsoConcrete_monoidality_eq
  {k : Type u}
  [Field k]
  {V W : FGModuleCat.{u} k} :
-- imply
  (vecDoubleDualIsoConcrete k (V ⊗ W)).hom = ((vecDoubleDualIsoConcrete k V).hom ⊗ₘ (vecDoubleDualIsoConcrete k W).hom) ≫ (vecTensorCoherenceIsoConcrete k V W).hom := by
-- proof
  apply vecDoubleDualIsoConcrete_monoidality k V W

/--
[vecDoubleDualIsoConcrete_dimUnit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecPivotalConcrete.lean)
-/
@[path]
private lemma vecDoubleDualIsoConcrete_dimUnit_eq
  {k : Type u}
  [Field k] :
-- imply
  leftQuantumTrace (FGModuleCat k) (vecDoubleDualIsoConcrete k (𝟙_ (FGModuleCat k))).hom = 𝟙 (𝟙_ (FGModuleCat k)) := by
-- proof
  apply vecDoubleDualIsoConcrete_dimUnit k


-- created on 2026-10-23
