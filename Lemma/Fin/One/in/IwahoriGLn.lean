import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.Building.IwahoriGLn
open Matrix DVRContext


/--
[one_mem_IwahoriGLn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLn.lean)
-/
@[path]
private lemma main
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ} :
-- imply
  (1 : GL (Fin n) C.k) ∈ IwahoriGLn C n := by
-- proof
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · simp only [Units.val_one, one_apply_eq]
    exact C.isUnitInO_one
  · have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
    simp only [Units.val_one, one_apply_ne hne]
    exact DVRClosure.isInO_zero
  · have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
    simp only [Units.val_one, one_apply_ne hne]
    exact C.isInMaxIdeal_zero



/--
[one_mem_LowerUnipGLn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLn.lean)
-/
private lemma one_mem_LowerUnipGLn
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ} :
-- imply
  (1 : GL (Fin n) C.k) ∈ LowerUnipGLn C n := by
-- proof
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp only [Units.val_one, one_apply_eq]
  · have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
    simp only [Units.val_one, one_apply_ne hne]



/--
[one_mem_UpperUnipGLn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLn.lean)
-/
private lemma one_mem_UpperUnipGLn
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ} :
-- imply
  (1 : GL (Fin n) C.k) ∈ UpperUnipGLn C n := by
-- proof
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp only [Units.val_one, one_apply_eq]
  · have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
    simp only [Units.val_one, one_apply_ne hne]



/--
[iwahoriDecompositionGLn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLn.lean)
-/
private lemma iwahoriDecompositionGLn
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ} :
-- imply
  ∀ b ∈ IwahoriGLn C n, ∃! (triple : GL (Fin n) C.k × GL (Fin n) C.k × GL (Fin n) C.k), let (u', m, u) := triple u' ∈ LowerUnipGLn C n ∩ IwahoriGLn C n ∧ m ∈ DiagGLn C n ∩ IwahoriGLn C n ∧ u ∈ UpperUnipGLn C n ∩ IwahoriGLn C n ∧ b = u' * m * u := by
-- proof
  intro b hb
  by_cases hn : n ≥ 2
  ·
    obtain ⟨⟨u', m, u⟩, hu'_mem, hm_mem, hu_mem, hb_eq⟩ :=
      C.IwahoriDecompositionGLn_existence n hn b hb
    refine ⟨⟨u', m, u⟩, ⟨hu'_mem, hm_mem, hu_mem, hb_eq⟩, ?_⟩
    rintro ⟨u'₂, m₂, u₂⟩ ⟨hu'₂_mem, hm₂_mem, hu₂_mem, hb_eq₂⟩
    have heq : u'₂ * m₂ * u₂ = u' * m * u := hb_eq₂.symm.trans hb_eq
    have ⟨h1, h2, h3⟩ := iwahori_decomp_unique u'₂ m₂ u₂ u' m u
      hu'₂_mem hm₂_mem hu₂_mem hu'_mem hm_mem hu_mem heq
    exact Prod.ext h1 (Prod.ext h2 h3)
  ·
    have hn_le : n ≤ 1 := by omega
    have h1_lower : (1 : GL (Fin n) C.k) ∈ LowerUnipGLn C n ∩ IwahoriGLn C n :=
      ⟨one_mem_LowerUnipGLn C n, one_mem_IwahoriGLn C n⟩
    have hb_diag : b ∈ DiagGLn C n ∩ IwahoriGLn C n := by
      refine ⟨fun i j hij => ?_, hb⟩
      interval_cases n
      · exact Fin.elim0 i
      · exact absurd (Subsingleton.elim i j) hij |> False.elim
    have h1_upper : (1 : GL (Fin n) C.k) ∈ UpperUnipGLn C n ∩ IwahoriGLn C n :=
      ⟨one_mem_UpperUnipGLn C n, one_mem_IwahoriGLn C n⟩
    have hb_eq : b = 1 * b * 1 := by simp
    refine ⟨⟨1, b, 1⟩, ⟨h1_lower, hb_diag, h1_upper, hb_eq⟩, ?_⟩
    rintro ⟨u'₂, m₂, u₂⟩ ⟨hu'₂_mem, hm₂_mem, hu₂_mem, hb_eq₂⟩
    have heq : u'₂ * m₂ * u₂ = 1 * b * 1 := hb_eq₂.symm.trans hb_eq
    have ⟨h1, h2, h3⟩ := iwahori_decomp_unique u'₂ m₂ u₂ 1 b 1
      hu'₂_mem hm₂_mem hu₂_mem h1_lower hb_diag h1_upper heq
    exact Prod.ext h1 (Prod.ext h2 h3)



-- created on 2026-10-23
-- updated on 2026-10-24
