import Mathlib
import Initialize.Tactic.Attr.Basic
open Finset Nat


namespace ErdosKoRado

/--
[erdos_ko_rado_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/ErdosKoRado.lean)
-/
@[path]
lemma erdos_ko_rado_theorem
  {n k : ℕ}
  {F : Finset (Finset (Fin n))}
-- given
  (hn : 2 * k ≤ n)
  (hF_int : (↑F : Set (Finset (Fin n))).Intersecting)
  (hF_sized : Set.Sized k (↑F : Set (Finset (Fin n)))) :
-- imply
  F.card ≤ (n - 1).choose (k - 1) :=
-- proof
  Finset.erdos_ko_rado hF_int hF_sized (by omega)

end ErdosKoRado


-- created on 2026-10-23
