import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.ClawFreeIndependencePoly
open MetaMathlibExt
open SimpleGraph


/--
[independence_poly_of_claw_free_splits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ClawFreeIndependencePoly.lean)
-/
@[path]
private lemma independence_poly_of_claw_free_splits_eq
  :
-- imply
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    clawFree G → ((independencePoly G).map (Int.castRingHom ℝ)).Splits := by
-- proof
  apply MetaMathlibExt.independence_poly_of_claw_free_splits

/--
[clawFree_iff_not_isIndContained](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ClawFreeIndependencePoly.lean)
-/
@[path]
private lemma clawFree_iff_not_isIndContained_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] :
-- imply
  clawFree G ↔ ¬ (SimpleGraph.starGraph (0 : Fin 4)).IsIndContained G := by
-- proof
  apply MetaMathlibExt.clawFree_iff_not_isIndContained G

/--
[independencePoly_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ClawFreeIndependencePoly.lean)
-/
@[path]
private lemma independencePoly_coeff_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ} :
-- imply
  (independencePoly G).coeff k = ((G.indepSetFinset k).card : ℤ) := by
-- proof
  apply MetaMathlibExt.independencePoly_coeff G k

/--
[aeval_independencePoly](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ClawFreeIndependencePoly.lean)
-/
@[path]
private lemma aeval_independencePoly_eq
  [Fintype V] [DecidableEq V] [CommRing R]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {x : R} :
-- imply
  Polynomial.aeval x (independencePoly G)
    = ∑ s ∈ Finset.univ.filter (fun s : Finset V => G.IsIndepSet (s : Set V)),
    x ^ s.card := by
-- proof
  apply MetaMathlibExt.aeval_independencePoly G x

/--
[independencePoly_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ClawFreeIndependencePoly.lean)
-/
@[path]
private lemma independencePoly_bot_eq
  [Fintype V] [DecidableEq V] :
-- imply
  independencePoly (⊥ : SimpleGraph V) = (1 + Polynomial.X) ^ Fintype.card V := by
-- proof
  apply MetaMathlibExt.independencePoly_bot

/--
[independencePoly_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ClawFreeIndependencePoly.lean)
-/
@[path]
private lemma independencePoly_top_eq
  [Fintype V] [DecidableEq V] :
-- imply
  independencePoly (⊤ : SimpleGraph V)
    = 1 + Polynomial.C (Fintype.card V : ℤ) * Polynomial.X := by
-- proof
  apply MetaMathlibExt.independencePoly_top

/--
[isClawFree_iff_not_isIndContained](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ClawFreeIndependencePoly.lean)
-/
@[path]
private lemma isClawFree_iff_not_isIndContained_eq
  {G : SimpleGraph V} :
-- imply
  G.IsClawFree ↔ ¬ (starGraph (0 : Fin 4)).IsIndContained G := by
-- proof
  apply SimpleGraph.isClawFree_iff_not_isIndContained G

/--
[clawFree_iff_isClawFree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ClawFreeIndependencePoly.lean)
-/
@[path]
private lemma clawFree_iff_isClawFree_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] :
-- imply
  clawFree G ↔ G.IsClawFree := by
-- proof
  apply MetaMathlibExt.clawFree_iff_isClawFree G


-- created on 2026-10-20
