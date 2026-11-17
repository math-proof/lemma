module

public import Mathlib
public import Class.v1.Atlas.TensorCategories.code.QuantumGroupGeneral

public section

open Coalgebra HopfAlgebra
open scoped TensorProduct


/--
[qAnalog_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumGroupGeneral.lean)
-/
public theorem qAnalog_one
  [Field k]
  {q : k}
-- given
  (hq : q - q⁻¹ ≠ 0) :
-- imply
  qAnalog q 1 = 1 := by
-- proof
  simp only [qAnalog, pow_one]
  exact div_self hq


-- created on 2026-10-23
