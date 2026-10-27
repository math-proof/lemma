import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.Building.IwahoriGLnBaseCase
open Matrix DVRContext


/--
[fin2_lt_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnBaseCase.lean)
-/
@[path]
private lemma main
  {C : DVRContext}
  [DVRClosureGL2 C]
  {i j : Fin 2} :
-- imply
  i.val < j.val ↔ (i = 0 ∧ j = 1) := by
-- proof
  constructor
  · intro h
    fin_cases i <;> fin_cases j <;> simp_all
  · rintro ⟨rfl, rfl⟩; norm_num



/--
[fin2_gt_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnBaseCase.lean)
-/
private lemma fin2_gt_iff
  {C : DVRContext}
  [DVRClosureGL2 C]
  {i j : Fin 2} :
-- imply
  i.val > j.val ↔ (i = 1 ∧ j = 0) := by
-- proof
  constructor
  · intro h
    fin_cases i <;> fin_cases j <;> simp_all
  · rintro ⟨rfl, rfl⟩; norm_num



/--
[iwahoriGLn_eq_iwahoriGL2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnBaseCase.lean)
-/
private lemma iwahoriGLn_eq_iwahoriGL2
  {C : DVRContext}
  [DVRClosureGL2 C] :
-- imply
  IwahoriGLn C 2 = IwahoriGL2 C := by
-- proof
  ext g
  simp only [IwahoriGLn, IwahoriGL2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hdiag, habove, hbelow⟩
    exact ⟨hdiag 0, hdiag 1,
      habove 0 1 (by norm_num),
      hbelow 1 0 (by norm_num)⟩
  · rintro ⟨h00, h11, h01, h10⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i; fin_cases i <;> assumption
    · intro i j hij
      rw [fin2_lt_iff] at hij
      obtain ⟨rfl, rfl⟩ := hij
      exact h01
    · intro i j hij
      rw [fin2_gt_iff] at hij
      obtain ⟨rfl, rfl⟩ := hij
      exact h10



/--
[upperUnipGLn_eq_upperUnipGL2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnBaseCase.lean)
-/
private lemma upperUnipGLn_eq_upperUnipGL2
  {C : DVRContext}
  [DVRClosureGL2 C] :
-- imply
  UpperUnipGLn C 2 = UpperUnipGL2 C := by
-- proof
  ext g
  simp only [UpperUnipGLn, UpperUnipGL2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hdiag, hbelow⟩
    exact ⟨hdiag 0, hdiag 1, hbelow 1 0 (by norm_num)⟩
  · rintro ⟨h00, h11, h10⟩
    refine ⟨?_, ?_⟩
    · intro i; fin_cases i <;> assumption
    · intro i j hij
      rw [fin2_gt_iff] at hij
      obtain ⟨rfl, rfl⟩ := hij
      exact h10



/--
[lowerUnipGLn_eq_lowerUnipGL2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnBaseCase.lean)
-/
private lemma lowerUnipGLn_eq_lowerUnipGL2
  {C : DVRContext}
  [DVRClosureGL2 C] :
-- imply
  LowerUnipGLn C 2 = LowerUnipGL2 C := by
-- proof
  ext g
  simp only [LowerUnipGLn, LowerUnipGL2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hdiag, habove⟩
    exact ⟨hdiag 0, hdiag 1, habove 0 1 (by norm_num)⟩
  · rintro ⟨h00, h11, h01⟩
    refine ⟨?_, ?_⟩
    · intro i; fin_cases i <;> assumption
    · intro i j hij
      rw [fin2_lt_iff] at hij
      obtain ⟨rfl, rfl⟩ := hij
      exact h01



/--
[diagGLn_eq_diagGL2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnBaseCase.lean)
-/
private lemma diagGLn_eq_diagGL2
  {C : DVRContext}
  [DVRClosureGL2 C] :
-- imply
  DiagGLn C 2 = DiagGL2 C := by
-- proof
  ext g
  simp only [DiagGLn, DiagGL2, Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨h 0 1 (by decide), h 1 0 (by decide)⟩
  · rintro ⟨h01, h10⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all



/--
[iwahoriDecompositionGLn_base_case](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnBaseCase.lean)
-/
private lemma iwahoriDecompositionGLn_base_case
  {C : DVRContext}
  [DVRClosureGL2 C] :
-- imply
  ∀ b ∈ IwahoriGLn C 2, ∃! (triple : GL (Fin 2) C.k × GL (Fin 2) C.k × GL (Fin 2) C.k), let (u', m, u) := triple u' ∈ LowerUnipGLn C 2 ∩ IwahoriGLn C 2 ∧ m ∈ DiagGLn C 2 ∩ IwahoriGLn C 2 ∧ u ∈ UpperUnipGLn C 2 ∩ IwahoriGLn C 2 ∧ b = u' * m * u := by
-- proof
  simp_rw [iwahoriGLn_eq_iwahoriGL2, lowerUnipGLn_eq_lowerUnipGL2,
    diagGLn_eq_diagGL2, upperUnipGLn_eq_upperUnipGL2]
  exact C.IwahoriDecomposition_concrete



-- created on 2026-10-23
-- updated on 2026-10-26
