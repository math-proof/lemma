import Def.Algebra.BigOperators.Products
import Def.Data.Tensor.Stack.Part2
import Def.Data.Tensor.Inv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Def.LinearAlgebra.Matrix.Matpow


noncomputable instance [CommRing α] [CharZero α] : HPow (Tensor α [m, m]) Int (Tensor α [m, m]) := ⟨Tensor.MatPow⟩

