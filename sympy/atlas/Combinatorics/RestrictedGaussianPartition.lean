/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RestrictedGaussianPartition.lean -/

import Mathlib.Algebra.IsPrimePow

namespace MetaMathlibExt

/-- A Gaussian partition type, represented by its nonincreasing list of
subspace dimensions. This small carrier is kept local to the substantive
restricted-Gaussian-partition development rather than published as a
standalone entry. -/
structure GaussianPartition where
  dims : List ℕ
  sorted_desc : List.Pairwise (· ≥ ·) dims

/-- A descending block `(d, m)` of an integer partition of `n`. -/
structure Block where
  d : Nat
  m : Nat
deriving DecidableEq, Repr

/-- One simultaneous split level: `c` copies of parent `a + b` become `c` copies
of `a` and `c * q ^ a` copies of `b`. -/
structure BranchStep where
  a : Nat
  b : Nat
  c : Nat
deriving DecidableEq, Repr

def blockWeight (B : Block) : Nat := B.m * B.d

def prefixAt (blocks : List Block) (i : Nat) : Nat :=
  ((blocks.take i).map blockWeight).sum

def blockAt (blocks : List Block) (i : Nat) : Block :=
  blocks[i]?.getD ⟨0, 0⟩

/-- Computed basic Gaussian multiplicity of block `i`:
`sum j < m_i, q ^ (prefix_i + j * d_i)`. -/
def basicCount (q : Nat) (blocks : List Block) (i : Nat) : Nat :=
  match blocks[i]? with
  | none => 0
  | some B => ((List.range B.m).map (fun j => q ^ (prefixAt blocks i + j * B.d))).sum

/-- First-split exponent `u = prefix_i + (m_i - 1) * d_i` for block `i`. -/
def branchBoundExp (blocks : List Block) (i : Nat) : Nat :=
  match blocks[i]? with
  | none => 0
  | some B => prefixAt blocks i + (B.m - 1) * B.d

def blockBasicDims (q : Nat) (blocks : List Block) (i : Nat) : List Nat :=
  match blocks[i]? with
  | none => []
  | some B => List.replicate (basicCount q blocks i) B.d

def basicSegs (q : Nat) (blocks : List Block) : List (List Nat) :=
  (List.range blocks.length).map (blockBasicDims q blocks)

def basicGlobalDims (q : Nat) (blocks : List Block) : List Nat :=
  (basicSegs q blocks).flatten

def chainAt (chains : List (List BranchStep)) (i : Nat) : List BranchStep :=
  match chains[i]? with
  | none => []
  | some ch => ch

/-- Remove the first `c` occurrences of `x`, returning the kept prefix before the
removal point and the remaining suffix. -/
def removeFirstNPos (x c : Nat) : List Nat → Option (List Nat × List Nat)
  | [] => if c = 0 then some ([], []) else none
  | y :: ys =>
    match c with
    | 0 => some ([], y :: ys)
    | n + 1 =>
      if y = x then removeFirstNPos x n ys
      else (removeFirstNPos x (n + 1) ys).map (fun p => (y :: p.1, p.2))

/-- Exact split replacement on dimension lists: the last `c` copies of `a + b`
are replaced in place by `c` copies of `a` followed by `c * q ^ a` copies of `b`.
No sorting is performed; sortedness is checked separately at every stage. -/
def applySplit (q a b c : Nat) (l : List Nat) : Option (List Nat) :=
  match removeFirstNPos (a + b) c l.reverse with
  | none => none
  | some (beforeRev, restRev) =>
    some (restRev.reverse ++ List.replicate c a ++
      List.replicate (c * q ^ a) b ++ beforeRev.reverse)

def applyChain (q : Nat) (l : List Nat) : List BranchStep → Option (List Nat)
  | [] => some l
  | s :: rest =>
    match applySplit q s.a s.b s.c l with
    | none => none
    | some l' => applyChain q l' rest

/-- Realize block `i` and its optional branch independently of all other blocks. -/
def blockFinalDims (q : Nat) (blocks : List Block)
    (chains : List (List BranchStep)) (i : Nat) : Option (List Nat) :=
  match chains[i]? with
  | none => none
  | some ch => applyChain q (blockBasicDims q blocks i) ch

def allFinalDimsAux (q : Nat) (blocks : List Block)
    (chains : List (List BranchStep)) : Nat → Option (List (List Nat))
  | 0 => some []
  | t + 1 =>
    match allFinalDimsAux q blocks chains t with
    | none => none
    | some acc =>
      match blockFinalDims q blocks chains t with
      | none => none
      | some cur => some (acc ++ [cur])

def allFinalDims (q : Nat) (blocks : List Block)
    (chains : List (List BranchStep)) : Option (List (List Nat)) :=
  allFinalDimsAux q blocks chains blocks.length

def sequenceOptSeg : List (Option (List Nat)) → Option (List (List Nat))
  | [] => some []
  | none :: _ => none
  | some x :: xs => (sequenceOptSeg xs).map (x :: ·)

/-- Global dimensions after completing blocks before `i`, applying the first `k + 1`
levels of block `i`, and leaving later blocks basic. Consecutive stages differ by
exactly one split replacement inside one block segment. -/
def stageSegments (q : Nat) (blocks : List Block) (chains : List (List BranchStep))
    (finals : List (List Nat)) (i k : Nat) : Option (List (List Nat)) :=
  sequenceOptSeg ((List.range blocks.length).map fun h =>
    if h < i then finals[h]?
    else if h = i then
      applyChain q (blockBasicDims q blocks h) ((chainAt chains h).take (k + 1))
    else some (blockBasicDims q blocks h))

def stageGlobalDims (q : Nat) (blocks : List Block) (chains : List (List BranchStep))
    (finals : List (List Nat)) (i k : Nat) : Option (List Nat) :=
  (stageSegments q blocks chains finals i k).map List.flatten

def BlocksStructValid (blocks : List Block) (n : Nat) : Prop :=
  (∀ B ∈ blocks, 1 ≤ B.d) ∧
  (∀ B ∈ blocks, 1 ≤ B.m) ∧
  (∀ p ∈ blocks.zip blocks.tail, p.1.d > p.2.d) ∧
  (blocks.map blockWeight).sum = n

instance decBlocksStructValid (blocks : List Block) (n : Nat) :
    Decidable (BlocksStructValid blocks n) := by
  unfold BlocksStructValid
  exact inferInstance

def ChainHeadValid (q : Nat) (blocks : List Block) (i : Nat) (s : BranchStep) : Prop :=
  1 ≤ s.b ∧ s.b ≤ s.a ∧ s.a + s.b = (blockAt blocks i).d ∧ 1 ≤ s.c ∧
    s.c ≤ q ^ branchBoundExp blocks i - 1 ∧ basicCount q blocks i ≠ 1

instance decChainHeadValid (q : Nat) (blocks : List Block) (i : Nat)
    (s : BranchStep) : Decidable (ChainHeadValid q blocks i s) := by
  unfold ChainHeadValid
  exact inferInstance

/-- Adjacent-level linkage only: each consecutive pair shares the left dimension
and satisfies the count bound. Zipping with the tail relates consecutive levels,
unlike `List.Pairwise`, which would relate every later pair. -/
def ChainAdjValid (ch : List BranchStep) : Prop :=
  ((ch.zip ch.tail).all (fun p =>
    decide (p.2.a + p.2.b = p.1.a ∧ 1 ≤ p.2.b ∧ p.2.b ≤ p.2.a ∧
      1 ≤ p.2.c ∧ p.2.c ≤ p.1.c)) = true)

instance decChainAdjValid (ch : List BranchStep) :
    Decidable (ChainAdjValid ch) := by
  unfold ChainAdjValid
  exact inferInstance

/-- Branch validity: the root-specific head condition applies to the FIRST step
only; every later step is constrained by the adjacent-chain condition over
consecutive pairs. An empty chain means no branch and is valid. -/
def BranchValid (q : Nat) (blocks : List Block) (i : Nat)
    (ch : List BranchStep) : Prop :=
  match ch with
  | [] => True
  | s :: _ => ChainHeadValid q blocks i s ∧ ChainAdjValid ch

instance decBranchValid (q : Nat) (blocks : List Block) (i : Nat)
    (ch : List BranchStep) : Decidable (BranchValid q blocks i ch) := by
  cases ch with
  | nil => exact isTrue True.intro
  | cons s rest =>
    exact inferInstanceAs
      (Decidable (ChainHeadValid q blocks i s ∧ ChainAdjValid (s :: rest)))

/-- A Gaussian partition `G` is a restricted Gaussian partition for prime power `q`
and positive `n` when its dimensions arise from valid descending blocks, each
realized independently with at most one nonempty simultaneous-split branch, every
intermediate global list stays nonincreasing, and the target equals the realized
final dimensions exactly. -/
def IsRestrictedGaussianPartition (q n : Nat) (G : GaussianPartition) : Prop :=
  IsPrimePow q ∧ 0 < n ∧
    ∃ (blocks : List Block) (chains : List (List BranchStep)),
      chains.length = blocks.length ∧
      BlocksStructValid blocks n ∧
      (∀ i, i < blocks.length → BranchValid q blocks i (chainAt chains i)) ∧
      ∃ (finals : List (List Nat)),
        allFinalDims q blocks chains = some finals ∧
        (basicGlobalDims q blocks).Pairwise (fun a b : Nat => a ≥ b) ∧
        finals.flatten.Pairwise (fun a b : Nat => a ≥ b) ∧
        (∀ i, i < blocks.length →
          ∀ k, k < (chainAt chains i).length →
            (stageGlobalDims q blocks chains finals i k).all
              (fun g => decide (g.Pairwise (fun a b : Nat => a ≥ b))) = true) ∧
        G.dims = finals.flatten

/-- Every valid basic ancestor (realized with no branches) is restricted. -/
theorem basic_ancestor_is_restricted (q n : Nat) (blocks : List Block)
    (G : GaussianPartition) (hq : IsPrimePow q) (hn : 0 < n)
    (hvalid : BlocksStructValid blocks n)
    (hsorted : (basicGlobalDims q blocks).Pairwise (fun a b : Nat => a ≥ b))
    (hdims : G.dims = basicGlobalDims q blocks) :
    IsRestrictedGaussianPartition q n G := by
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
    rw [hch i hi]
    exact True.intro
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
