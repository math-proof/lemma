import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.ScalingLemma
open ValuationSubring


/--
[scaling_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ScalingLemma.lean)
-/
@[path]
lemma scaling_lemma
  [Field K]
  {A : ValuationSubring K}
  {n : ℕ}
  {x : Fin (n + 1) → K}
-- given
  (hx : ∀ i, x i ≠ 0) :
-- imply
  ∃ (l : K) (_ : l ≠ 0) (hmem : ∀ i, l * x i ∈ A), ∃ i, IsUnit (⟨l * x i, hmem i⟩ : A) := by
-- proof
  induction n with
  | zero =>
    have hmem : ∀ i : Fin 1, (x 0)⁻¹ * x i ∈ A := fun i => by
      have : i = 0 := Fin.ext (Fin.val_eq_zero i)
      rw [this, inv_mul_cancel₀ (hx 0)]; exact A.one_mem
    refine ⟨(x 0)⁻¹, inv_ne_zero (hx 0), hmem, ⟨0, ?_⟩⟩
    have h1 : (x 0)⁻¹ * x 0 = 1 := inv_mul_cancel₀ (hx 0)
    have : (⟨(x 0)⁻¹ * x 0, hmem 0⟩ : A) = 1 := Subtype.ext h1
    rw [this]; exact isUnit_one
  | succ m ih =>
    have hx' : ∀ i : Fin (m + 1), (x ∘ Fin.castSucc) i ≠ 0 := fun i => hx _
    obtain ⟨l, hl, hmem_old, i₀, hunit_old⟩ := ih (x ∘ Fin.castSucc) hx'
    by_cases hlast : l * x (Fin.last (m + 1)) ∈ A
    ·
      have hmem : ∀ i : Fin (m + 2), l * x i ∈ A := fun i =>
        Fin.lastCases hlast (fun j => hmem_old j) i
      refine ⟨l, hl, hmem, ⟨Fin.castSucc i₀, ?_⟩⟩
      exact hunit_old
    ·
      have hinv : (l * x (Fin.last (m + 1)))⁻¹ ∈ A :=
        (A.mem_or_inv_mem (l * x (Fin.last (m + 1)))).resolve_left hlast
      set xlast := x (Fin.last (m + 1)) with xlast_def
      have hxlast_ne : xlast ≠ 0 := hx (Fin.last (m + 1))
      have hmem : ∀ i : Fin (m + 2), xlast⁻¹ * x i ∈ A := fun i => by
        refine Fin.lastCases ?_ (fun j => ?_) i
        ·
          rw [inv_mul_cancel₀ hxlast_ne]; exact A.one_mem
        ·
          have key : xlast⁻¹ * x (Fin.castSucc j) =
            (l * x (Fin.castSucc j)) * (l * xlast)⁻¹ := by field_simp
          rw [key]; exact A.mul_mem _ _ (hmem_old j) hinv
      refine ⟨xlast⁻¹, inv_ne_zero hxlast_ne, hmem, ⟨Fin.last (m + 1), ?_⟩⟩
      have h1 : xlast⁻¹ * xlast = 1 := inv_mul_cancel₀ hxlast_ne
      have : (⟨xlast⁻¹ * xlast, hmem (Fin.last (m + 1))⟩ : A) = 1 := Subtype.ext h1
      rw [this]; exact isUnit_one


-- created on 2026-10-23
