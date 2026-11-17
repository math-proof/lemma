/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/SquarefreeTotient.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Tactic
public import Def.NumberTheory.PrimeCounting.SquarefreeTotient

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeCounting

instance (n : ℕ) : Decidable (btSmallSquarefree n) := by
  unfold btSmallSquarefree
  infer_instance

end MathlibExt.NumberTheory.PrimeCounting
