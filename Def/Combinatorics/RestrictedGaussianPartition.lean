/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RestrictedGaussianPartition.lean -/

import Mathlib.Algebra.IsPrimePow
import Structure.Combinatorics.RestrictedGaussianPartition


namespace MetaMathlibExt

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

end MetaMathlibExt
