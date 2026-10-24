import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.RestrictedGaussianPartition
open MetaMathlibExt


namespace MetaMathlibExt

/--
[basic_ancestor_is_restricted](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RestrictedGaussianPartition.lean)
-/
@[path]
lemma basic_ancestor_is_restricted
  {q n : Nat}
  {blocks : List Block}
  {G : GaussianPartition}
-- given
  (hq : IsPrimePow q)
  (hn : 0 < n)
  (hvalid : BlocksStructValid blocks n)
  (hsorted : (basicGlobalDims q blocks).Pairwise (fun a b : Nat => a ≥ b))
  (hdims : G.dims = basicGlobalDims q blocks) :
-- imply
  IsRestrictedGaussianPartition q n G := by
-- proof
  have hrep : ∀ (m i : Nat),
    i < m → (List.replicate m ([] : List BranchStep))[i]? = some [] := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
    | succ m ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ i => exact ih i (by omega)
  have hch : ∀ i, i < blocks.length →
    chainAt (List.replicate blocks.length []) i = [] := by
    intro i hi
    simp only [chainAt, hrep _ _ hi]
  have hfin : ∀ t, t ≤ blocks.length →
    allFinalDimsAux q blocks (List.replicate blocks.length []) t =
      some ((List.range t).map (blockBasicDims q blocks)) := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      have hlt : t < blocks.length := by omega
      have hbt : blockFinalDims q blocks (List.replicate blocks.length []) t =
        some (blockBasicDims q blocks t) := by
        simp only [blockFinalDims, applyChain, hrep _ _ hlt]
      have ht' : t ≤ blocks.length := by omega
      have haux := ih ht'
      simp only [allFinalDimsAux, haux, hbt, List.range_succ, List.map_append,
        List.map_cons, List.map_nil]
  have hbranch : ∀ i, i < blocks.length →
    BranchValid q blocks i (chainAt (List.replicate blocks.length []) i) := by
    intro i hi
    rwa [hch i hi]
  have hstage : ∀ i, i < blocks.length → ∀ k,
    k < (chainAt (List.replicate blocks.length []) i).length →
    (stageGlobalDims q blocks (List.replicate blocks.length [])
      (basicSegs q blocks) i k).all
      (fun g => decide (g.Pairwise (fun a b : Nat => a ≥ b))) = true := by
    intro i hi k hk
    have hnil : ([] : List BranchStep).length = 0 := rfl
    rw [hch i hi, hnil] at hk
    exact absurd hk (Nat.not_lt_zero k)
  refine ⟨hq, hn, blocks, List.replicate blocks.length ([] : List BranchStep),
    List.length_replicate, hvalid, hbranch, basicSegs q blocks, hfin _ le_rfl,
    hsorted, hsorted, hstage, hdims⟩

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
