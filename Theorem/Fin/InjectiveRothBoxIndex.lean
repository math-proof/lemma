module

public import Mathlib
public import Theorem.Fin.EqRothBoxIndex.of.RothBox

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothBoxIndex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.InjectiveRothBoxIndex
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
