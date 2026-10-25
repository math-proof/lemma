import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.Building.IwahoriGLnExistence
open Matrix DVRContext


namespace DVRContext

/--
[iwahoriDecompositionGLn_base_case_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnExistence.lean)
-/
@[path]
lemma iwahoriDecompositionGLn_base_case_exists
  {C : DVRContext}
  [DVRClosureGL2 C] :
-- imply
  ∀ b ∈ IwahoriGLn C 2, ∃ (triple : GL (Fin 2) C.k × GL (Fin 2) C.k × GL (Fin 2) C.k), let (u', m, u) := triple u' ∈ LowerUnipGLn C 2 ∩ IwahoriGLn C 2 ∧ m ∈ DiagGLn C 2 ∩ IwahoriGLn C 2 ∧ u ∈ UpperUnipGLn C 2 ∩ IwahoriGLn C 2 ∧ b = u' * m * u :=
-- proof
  fun b hb => (C.iwahoriDecompositionGLn_base_case b hb).exists

end DVRContext

namespace DVRContext

/--
[IwahoriDecompositionGLn_existence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnExistence.lean)
-/
@[path]
lemma IwahoriDecompositionGLn_existence
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
-- given
  (hn : n ≥ 2) :
-- imply
  ∀ b ∈ IwahoriGLn C n, ∃ (triple : GL (Fin n) C.k × GL (Fin n) C.k × GL (Fin n) C.k), let (u', m, u) := triple u' ∈ LowerUnipGLn C n ∩ IwahoriGLn C n ∧ m ∈ DiagGLn C n ∩ IwahoriGLn C n ∧ u ∈ UpperUnipGLn C n ∩ IwahoriGLn C n ∧ b = u' * m * u := by
-- proof
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm_eq : m + 1 = 2
    ·
      have hm : m = 1 := by omega
      subst hm
      exact C.iwahoriDecompositionGLn_base_case_exists
    ·
      have hm_ge2 : m ≥ 2 := by omega
      have hm_ge1 : m ≥ 1 := by omega
      have ih_m : ∀ b ∈ IwahoriGLn C m,
        ∃ (triple : GL (Fin m) C.k × GL (Fin m) C.k × GL (Fin m) C.k),
          let (u', md, u) := triple
          u' ∈ LowerUnipGLn C m ∩ IwahoriGLn C m ∧
          md ∈ DiagGLn C m ∩ IwahoriGLn C m ∧
          u ∈ UpperUnipGLn C m ∩ IwahoriGLn C m ∧
          b = u' * md * u := ih hm_ge2
      intro b hb
      exact C.iwahori_inductive_step hm_ge1 b hb ih_m

end DVRContext


-- created on 2026-10-23
