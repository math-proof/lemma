module

public import Def.Algebra.BigOperators.Products
public import Def.Data.Tensor.Stack.Part2
public import Def.Data.Tensor.Inv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Def.LinearAlgebra.Matrix.Matpow
@[expose] public section

noncomputable instance [CommRing α] [CharZero α] : HPow (Tensor α [m, m]) Int (Tensor α [m, m]) := ⟨Tensor.MatPow⟩

