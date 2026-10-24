/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerTreeEntropy.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.MergeCost
import sympy.atlas.CPythonListsort.Code.Assembly.PowerEntropyBound

/-!
# Entropy bound for a source-faithful PowerSort merge tree

This module is the pure bridge between the transcribed node-power arithmetic
and the implementation-independent merge-cost accounting.  A valid tree has
positive leaves laid out contiguously in source order.  Every internal label is
the actual `powerloop` result for the two aggregate child spans, and internal
labels strictly increase from a parent to each internal child.  The latter is
the min-Cartesian heap property used by Munro--Wild.

No fact about the implementation trace is assumed here.  A later bridge only
has to construct `PowerMergePlanValid` for the tree replayed from that trace.
-/

namespace CPythonListsort

namespace MergeTree

/-- The label at an internal root, if the tree is not a leaf. -/
def rootPower : MergeTree → Option Nat
  | .leaf _ => none
  | .merge power _ _ => some power

/-- Source-faithful validity of a power-labelled ordered merge tree.

`listBase` is the absolute base of the complete input, `listLength` is its
finite-width length, and `base` is the absolute base of this subtree.  The
recursive bases force the leaves to be contiguous and in source order.  At an
internal node, `power` is exactly the transcribed `powerloop` result for the
aggregate left and right spans.  The final two clauses are the strict
min-Cartesian heap condition for internal children; leaves carry no node
power. -/
def PowerValid (listBase : Nat) (listLength : PySSize) :
    Nat → MergeTree → Prop
  | base, .leaf length =>
      listBase ≤ base ∧
        base + length ≤ listBase + listLength.toNat ∧
        0 < length
  | base, .merge power left right =>
      listBase ≤ base ∧
        base + left.totalLength + right.totalLength ≤
          listBase + listLength.toNat ∧
        PowerValid listBase listLength base left ∧
        PowerValid listBase listLength (base + left.totalLength) right ∧
        ValidPowerloopInput
          (BitVec.ofNat 64 (base - listBase))
          (BitVec.ofNat 64 left.totalLength)
          (BitVec.ofNat 64 right.totalLength)
          listLength ∧
        power = powerloop
          (BitVec.ofNat 64 (base - listBase))
          (BitVec.ofNat 64 left.totalLength)
          (BitVec.ofNat 64 right.totalLength)
          listLength ∧
        (∀ childPower, left.rootPower = some childPower → power < childPower) ∧
        (∀ childPower, right.rootPower = some childPower → power < childPower)

/-- Validity of a complete PowerSort merge plan.  Empty input is represented
by `MergePlan.empty`; a nonempty input is represented by one complete ordered
tree rooted at the input base. -/
def PowerMergePlanValid (listBase : Nat) (listLength : PySSize) :
    MergePlan → Prop
  | .empty => listLength.toNat = 0
  | .tree root =>
      root.PowerValid listBase listLength listBase ∧
        root.totalLength = listLength.toNat

/-- The run lengths of a valid power plan form a positive profile of the
complete input length. -/
def PowerMergePlanValid.runProfile
    {listBase : Nat} {listLength : PySSize} {plan : MergePlan}
    (hvalid : PowerMergePlanValid listBase listLength plan) :
    RunProfile listLength.toNat where
  lengths := plan.runLengths
  sum_eq := by
    cases plan with
    | empty => simpa [MergePlan.runLengths] using hvalid.symm
    | tree root =>
        simpa [MergePlan.runLengths, MergeTree.sum_runLengths] using hvalid.2
  positive := by
    cases plan with
    | empty => simp [MergePlan.runLengths]
    | tree root =>
        simpa [MergePlan.runLengths] using hvalid.1.leaf_positive
