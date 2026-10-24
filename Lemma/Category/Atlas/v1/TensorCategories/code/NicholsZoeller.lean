import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.NicholsZoeller


/--
[SubQuasiHopfAlgebra.module_finite_KH](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/NicholsZoeller.lean)
-/
@[path]
lemma SubQuasiHopfAlgebra.module_finite_KH
  {k : Type u}
  {H : Type v}
  [Field k]
  [Ring H]
  [Algebra k H]
  [QuasiHopfAlgebra k H] :
-- imply
  Module.Finite K H :=
-- proof
  Module.Finite.of_restrictScalars_finite k K H
/-- The dimension of a sub-quasi-Hopf algebra divides the dimension of the ambient
quasi-Hopf algebra, derived from freeness via Nichols-Zoeller. -/
section QuasiHopfFreenessConsequences
variable (k : Type u) (H : Type v) [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H]
  [FiniteDimensional k H]
  (K : SubQuasiHopfAlgebra k H) [QuasiHopfFreeness k H K]

/--
[QuasiHopfFreeness.free'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/NicholsZoeller.lean)
-/
@[path]
lemma QuasiHopfFreeness.free'
  {k : Type u}
  {H : Type v}
  [Field k]
  [Ring H]
  [Algebra k H]
  [QuasiHopfAlgebra k H] :
-- imply
  Module.Free K H :=
-- proof
  QuasiHopfFreeness.free

/--
[QuasiHopfFreeness.finite'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/NicholsZoeller.lean)
-/
@[path]
lemma QuasiHopfFreeness.finite'
  {k : Type u}
  {H : Type v}
  [Field k]
  [Ring H]
  [Algebra k H]
  [QuasiHopfAlgebra k H] :
-- imply
  Module.Finite K H :=
-- proof
  QuasiHopfFreeness.finite

/--
[QuasiHopfFreeness.finrank_dvd'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/NicholsZoeller.lean)
-/
@[path]
lemma QuasiHopfFreeness.finrank_dvd'
  {k : Type u}
  {H : Type v}
  [Field k]
  [Ring H]
  [Algebra k H]
  [QuasiHopfAlgebra k H] :
-- imply
  Module.finrank k K ∣ Module.finrank k H :=
-- proof
  QuasiHopfFreeness.finrank_dvd
/-- The dimension of a sub-quasi-Hopf algebra is at most the dimension of the ambient
quasi-Hopf algebra. -/
end QuasiHopfFreenessConsequences

/--
[SubHopfAlgebra.module_finite_KH](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/NicholsZoeller.lean)
-/
@[path]
lemma SubHopfAlgebra.module_finite_KH
  {k : Type u}
  {H : Type v}
  [Field k]
  [Ring H]
  [HopfAlgebra k H] :
-- imply
  Module.Finite K H :=
-- proof
  Module.Finite.of_restrictScalars_finite k K H
/-- If `H` is free over a sub-Hopf algebra `K`, then `dim_k K` divides `dim_k H`. -/
section NicholsZoellerConsequences
variable (k : Type u) (H : Type v) [Field k] [Ring H] [HopfAlgebra k H]
  [FiniteDimensional k H]
  (K : SubHopfAlgebra k H) [NicholsZoellerFreeness k H K]

/--
[NicholsZoeller.finrank_eq_mul_div](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/NicholsZoeller.lean)
-/
@[path]
lemma NicholsZoeller.finrank_eq_mul_div
  {k : Type u}
  {H : Type v}
  [Field k]
  [Ring H]
  [HopfAlgebra k H] :
-- imply
  Module.finrank k H = Module.finrank k K * (Module.finrank k H / Module.finrank k K) :=
-- proof
  Nat.eq_mul_of_div_eq_right (NicholsZoeller.finrank_dvd k H K) rfl
end NicholsZoellerConsequences

/--
[NicholsZoeller.free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/NicholsZoeller.lean)
-/
@[path]
private lemma free_eq
  {k : Type u}
  {H : Type v}
  [Field k]
  [Ring H]
  [HopfAlgebra k H] :
-- imply
  Module.Free K H := by
-- proof
  apply NicholsZoeller.free k H

/--
[NicholsZoeller.finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/NicholsZoeller.lean)
-/
@[path]
private lemma finite_eq
  {k : Type u}
  {H : Type v}
  [Field k]
  [Ring H]
  [HopfAlgebra k H] :
-- imply
  Module.Finite K H := by
-- proof
  apply NicholsZoeller.finite k H

/--
[NicholsZoeller.finrank_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/NicholsZoeller.lean)
-/
@[path]
private lemma finrank_dvd_eq
  {k : Type u}
  {H : Type v}
  [Field k]
  [Ring H]
  [HopfAlgebra k H] :
-- imply
  Module.finrank k K ∣ Module.finrank k H := by
-- proof
  apply NicholsZoeller.finrank_dvd k H


-- created on 2026-10-23
