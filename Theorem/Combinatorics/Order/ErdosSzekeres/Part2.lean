/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean -/

import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Instance.Combinatorics.Order.ErdosSzekeres


namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/-- No strict pair exists in `Fin 1`. -/
theorem fin1_false {i j : Fin 1} (hij : i < j) : False := by
  have hiv : i.val < j.val := Fin.lt_def.mp hij
  have h1 := i.isLt
  have h2 := j.isLt
  omega

/-- Singletons are increasing subsequences. -/
theorem singleton_incr {N : ℕ} (f : Fin N → ℝ) (p : Fin N) :
    IsIncrSubseq f 1 (fun _ => p) :=
  ⟨fun _ _ hij => False.elim (fin1_false hij),
    fun _ _ hij => False.elim (fin1_false hij)⟩

/-- Singletons are decreasing subsequences. -/
theorem singleton_decr {N : ℕ} (f : Fin N → ℝ) (p : Fin N) :
    IsDecrSubseq f 1 (fun _ => p) :=
  ⟨fun _ _ hij => False.elim (fin1_false hij),
    fun _ _ hij => False.elim (fin1_false hij)⟩

end MathlibExt.Combinatorics.Order.ErdosSzekeres
