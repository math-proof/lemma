import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper
open Equiv Fin Function


/--
[typeA_relations_satisfied](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAInjectivityHelper.lean)
-/
@[path]
private lemma main
  {n : ℕ} :
-- imply
  ∀ r ∈ (CoxeterMatrix.A n).relationsSet, (FreeGroup.lift (fun (i : Fin n) => swap (castSucc i) (succ i))) r = 1 := by
-- proof
  intro r ⟨⟨i, j⟩, hrij⟩
  rw [← hrij]
  simp only [uncurry, CoxeterMatrix.relation, map_pow, map_mul, FreeGroup.lift_apply_of]
  exact adjTransp_isLiftable n i j

/--
[typeA_toPermHom_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAInjectivityHelper.lean)
-/
private lemma typeA_toPermHom_surjective
  {n : ℕ}
-- given
  (h : ∀ r ∈ (CoxeterMatrix.A n).relationsSet, (FreeGroup.lift (fun (i : Fin n) => swap (castSucc i) (succ i))) r = 1) :
-- imply
  Function.Surjective (PresentedGroup.toGroup h : (CoxeterMatrix.A n).Group →* Equiv.Perm (Fin (n + 1))) := by
-- proof
  set φ := (PresentedGroup.toGroup h : (CoxeterMatrix.A n).Group →* Equiv.Perm (Fin (n + 1)))
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  have hgen : ∀ i : Fin n, swap (castSucc i) (succ i) ∈ φ.range := fun i =>
    MonoidHom.mem_range.mpr ⟨PresentedGroup.of i, PresentedGroup.toGroup.of h⟩
  intro σ _
  have hmcl := Equiv.Perm.mclosure_swap_castSucc_succ n
  have hσ : σ ∈ Submonoid.closure
    (Set.range fun i : Fin n => Equiv.swap (Fin.castSucc i) (Fin.succ i)) := by
    rw [hmcl]; exact Submonoid.mem_top σ
  apply (Submonoid.closure_le.mpr _) hσ
  intro x hx
  obtain ⟨i, hi⟩ := hx
  rw [← hi]
  exact hgen i
/-- Exact cardinality: $|W(A_{n-1})| = (n+1)!$, matching $|S_{n+1}|$. -/

/--
[swap_mul_swap_cube](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAInjectivityHelper.lean)
-/
private lemma swap_mul_swap_cube_eq
  [DecidableEq α]
  {a b c : α}
-- given
  (hab : a ≠ b)
  (hbc : b ≠ c)
  (hac : a ≠ c) :
-- imply
  (swap a b * swap b c) ^ 3 = 1 := by
-- proof
  apply swap_mul_swap_cube hab hbc hac

/--
[swap_mul_swap_cube'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAInjectivityHelper.lean)
-/
private lemma swap_mul_swap_cube'_eq
  [DecidableEq α]
  {a b c : α}
-- given
  (hab : a ≠ b)
  (hbc : b ≠ c)
  (hac : a ≠ c) :
-- imply
  (swap b c * swap a b) ^ 3 = 1 := by
-- proof
  apply swap_mul_swap_cube' hab hbc hac

/--
[adjTransp_isLiftable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAInjectivityHelper.lean)
-/
private lemma adjTransp_isLiftable_eq
  {n : ℕ} :
-- imply
  (CoxeterMatrix.A n).IsLiftable (fun i : Fin n => swap (castSucc i) (succ i)) := by
-- proof
  apply adjTransp_isLiftable n


-- created on 2026-10-23
-- updated on 2026-10-24
