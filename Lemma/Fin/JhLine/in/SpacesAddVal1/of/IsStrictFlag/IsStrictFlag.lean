import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.JordanHolderFrame.Part2
open GLnBuilding


/--
[jhLine_mem_Vi_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderFrame.lean)
-/
@[path]
private lemma jhLine_mem_Vi_succ_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin n}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag) :
-- imply
  jhLine σ τ hσ hτ i ∈ σ.spaces ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
-- proof
  apply GLnBuilding.jhLine_mem_Vi_succ σ τ hσ hτ i

/--
[jhLine_not_mem_Vi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderFrame.lean)
-/
@[path]
private lemma jhLine_not_mem_Vi_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin n}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag) :
-- imply
  jhLine σ τ hσ hτ i ∉ σ.spaces ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
-- proof
  apply GLnBuilding.jhLine_not_mem_Vi σ τ hσ hτ i

/--
[jhLine_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderFrame.lean)
-/
@[path]
private lemma jhLine_ne_zero_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin n}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag) :
-- imply
  jhLine σ τ hσ hτ i ≠ 0 := by
-- proof
  apply GLnBuilding.jhLine_ne_zero σ τ hσ hτ i

/--
[jhLine_mem_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderFrame.lean)
-/
@[path]
private lemma jhLine_mem_of_le_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin n}
  {j : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag)
  (hij : i.val + 1 ≤ j.val) :
-- imply
  jhLine σ τ hσ hτ i ∈ σ.spaces j := by
-- proof
  apply GLnBuilding.jhLine_mem_of_le σ τ hσ hτ i j hij

/--
[jhLine_linearIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderFrame.lean)
-/
@[path]
private lemma jhLine_linearIndependent_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag) :
-- imply
  LinearIndependent k (fun i : Fin n => jhLine σ τ hσ hτ i) := by
-- proof
  apply GLnBuilding.jhLine_linearIndependent σ τ hσ hτ

/--
[jhLine_span_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderFrame.lean)
-/
@[path]
private lemma jhLine_span_eq_top_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  [FiniteDimensional k (Vec k n)]
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag) :
-- imply
  Submodule.span k (Set.range (fun i : Fin n => jhLine σ τ hσ hτ i)) = ⊤ := by
-- proof
  apply GLnBuilding.jhLine_span_eq_top σ τ hσ hτ

/--
[jordanHolderFrame_compatible_sigma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderFrame.lean)
-/
@[path]
private lemma jordanHolderFrame_compatible_sigma_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  [FiniteDimensional k (Vec k n)]
  {i : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag) :
-- imply
  (jordanHolderFrame σ τ hσ hτ).IsCompatible k n (σ.spaces i) := by
-- proof
  apply GLnBuilding.jordanHolderFrame_compatible_sigma σ τ hσ hτ i


-- created on 2026-10-23
