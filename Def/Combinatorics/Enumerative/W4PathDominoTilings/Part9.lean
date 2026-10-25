/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.W4PathDominoTilings.Part6
open SimpleGraph


section

namespace MetaMathlibExt

noncomputable def buildTiling (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) : ∀ k : ℕ, k ≤ m → Tiling k (topHoles m M hM k)
  | 0, _ => ⟨rfl⟩
  | (k + 1), hk =>
    have hk' : k ≤ m := by omega
    have hkm : k < m := by omega
    have ih := buildTiling m M hM k hk'
    have hdisj : Disjoint (topHoles m M hM k) (topHoles m M hM (k + 1)) :=
      below_above_disjoint m M hM k hkm
    have hhor : HorizPairing (Finset.univ \ (topHoles m M hM k ∪ topHoles m M hM (k + 1))) :=
      horizPairingOf m M hM k hkm
    ⟨topHoles m M hM k, ⟨hdisj⟩, ih, hhor⟩

noncomputable def fwdTiling (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) : Tiling m ∅ := by
  cases m with
  | zero =>
    have htop : topHoles 0 M hM 0 = ∅ := rfl
    exact htop.rec (buildTiling 0 M hM 0 (by omega))
  | succ m =>
    have htop : topHoles (m + 1) M hM (m + 1) = ∅ := by
      change vertSet (m + 1) M hM m = ∅
      apply vertSet_top_empty
      omega
    exact htop.rec (buildTiling (m + 1) M hM (m + 1) (by omega))

-- Unpack vertical boundaries from a tiling: above of layer `j`.
def getS : ∀ (m : ℕ) (S' : Finset (Fin 4)), Tiling m S' → ℕ → Finset (Fin 4)
  | 0, _, _, _ => ∅
  | (m + 1), S', ⟨S, _, t, _⟩, j => if j = m then S' else getS m S t j

-- Unpack horizontal functions from a tiling.
def getF : ∀ (m : ℕ) (S' : Finset (Fin 4)), Tiling m S' → ℕ → (Fin 4 → Fin 4)
  | 0, _, _, _ => id
  | (m + 1), _, ⟨_, _, t, h⟩, j => if j = m then h.val else getF m _ t j

end MetaMathlibExt
end
