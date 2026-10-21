import Mathlib
import Lemma.Fin.EqRothBoxIndex.of.RothBox
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothBoxIndex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} {r : Fin m → ℕ} :
-- imply
  Function.Injective (rothBoxIndex : RothBox r → RothMvIndex m) := by
-- proof
  intro i j hij
  funext h
  apply Fin.ext
  simpa only [EqRothBoxIndex.of.RothBox] using
    congrArg (fun k : RothMvIndex m ↦ k h) hij


-- created on 2026-10-21
