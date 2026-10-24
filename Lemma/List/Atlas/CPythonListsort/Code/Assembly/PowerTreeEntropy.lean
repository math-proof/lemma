import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Assembly.PowerTreeEntropy
open CPythonListsort CPythonListsort.MergeTree


namespace CPythonListsort.MergeTree

/--
[PowerValid.leaf_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerTreeEntropy.lean)
-/
@[path]
lemma PowerValid.leaf_positive
  {listBase base : Nat}
  {listLength : PySSize}
  {tree : MergeTree}
-- given
  (hvalid : tree.PowerValid listBase listLength base) :
-- imply
  ∀ length ∈ tree.runLengths, 0 < length := by
-- proof
  induction tree generalizing base with
  | leaf length =>
    intro candidate hcandidate
    simp only [runLengths, List.mem_singleton] at hcandidate
    subst candidate
    exact hvalid.2.2
  | merge power left right ihLeft ihRight =>
    intro length hlength
    simp only [runLengths, List.mem_append] at hlength
    obtain hleft | hright := hlength
    · exact ihLeft hvalid.2.2.1 length hleft
    · exact ihRight hvalid.2.2.2.1 length hright

end CPythonListsort.MergeTree

namespace CPythonListsort.MergeTree

/--
[ofNat64_toNat_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerTreeEntropy.lean)
-/
@[path]
private lemma ofNat64_toNat_of_lt {x : Nat} (hx : x < 2 ^ 64) :
  (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

end CPythonListsort.MergeTree

namespace CPythonListsort.MergeTree

/--
[PowerValid.nodePower_lt_logb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerTreeEntropy.lean)
-/
@[path]
lemma PowerValid.nodePower_lt_logb
  {listBase base : Nat}
  {listLength : PySSize}
  {power : Nat}
  {left right : MergeTree}
  {leafLength : Nat}
-- given
  (hvalid : PowerValid listBase listLength base (.merge power left right))
  (hleaf : 0 < leafLength)
  (hleafSpan : leafLength ≤ left.totalLength + right.totalLength) :
-- imply
  (power : Real) < Real.logb 2 ((listLength.toNat : Real) / (leafLength : Real)) + 2 := by
-- proof
  rcases hvalid with
    ⟨hbase, hwithin, _hleft, _hright, hinput, hpower, _⟩
  have hspan : left.totalLength + right.totalLength ≤ listLength.toNat := by
    omega
  have hleft64 : left.totalLength < 2 ^ 64 :=
    lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hspan) listLength.isLt
  have hright64 : right.totalLength < 2 ^ 64 :=
    lt_of_le_of_lt (le_trans (Nat.le_add_left _ _) hspan) listLength.isLt
  have hleftExact : (BitVec.ofNat 64 left.totalLength).toNat =
    left.totalLength := ofNat64_toNat_of_lt hleft64
  have hrightExact : (BitVec.ofNat 64 right.totalLength).toNat =
    right.totalLength := ofNat64_toNat_of_lt hright64
  rw [hpower]
  apply powerloop_lt_logb_component_add_two
    (BitVec.ofNat 64 (base - listBase))
    (BitVec.ofNat 64 left.totalLength)
    (BitVec.ofNat 64 right.totalLength)
    listLength leafLength hinput hleaf
  simpa only [hleftExact, hrightExact] using hleafSpan

end CPythonListsort.MergeTree

namespace CPythonListsort.MergeTree

/--
[internal_leaf_depth_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerTreeEntropy.lean)
-/
@[path]
Munro--Wild per-leaf depth bound, provided the root label is at least
`depth + 1`.  Strictly increasing child labels preserve that premise down the
tree. -/
private lemma PowerValid.internal_leaf_depth_bound
  {listBase base : Nat} {listLength : PySSize}
  {tree : MergeTree} {depth : Nat}
  (hvalid : PowerValid listBase listLength base tree)
  (hinternal : tree.rootPower ≠ none)
  (hdepth : ∀ power, tree.rootPower = some power → depth + 1 ≤ power) :
  ∀ leaf ∈ tree.leavesWithDepth depth,
    (leaf.2 : Real) ≤
      Real.logb 2
        ((listLength.toNat : Real) / (leaf.1 : Real)) + 2 := by
  induction tree generalizing base depth with
  | leaf length => simp [rootPower] at hinternal
  | merge power left right ihLeft ihRight =>
    rcases hvalid with
      ⟨hbase, hwithin, hleftValid, hrightValid, hinput, hpower,
        hleftHeap, hrightHeap⟩
    have hrootDepth : depth + 1 ≤ power :=
      hdepth power (by simp [rootPower])
    intro leaf hleaf
    simp only [leavesWithDepth, List.mem_append] at hleaf
    obtain hleaf | hleaf := hleaf
    · by_cases hleftLeaf : left.rootPower = none
      · cases left with
        | leaf length =>
          simp only [leavesWithDepth, List.mem_singleton] at hleaf
          subst leaf
          have hlog := PowerValid.nodePower_lt_logb
            ⟨hbase, hwithin, hleftValid, hrightValid, hinput, hpower,
              hleftHeap, hrightHeap⟩
            hleftValid.2.2
            (show length ≤ length + right.totalLength by omega)
          norm_num only [Prod.fst, Prod.snd]
          exact le_trans (by exact_mod_cast hrootDepth) hlog.le
        | merge childPower childLeft childRight =>
          simp [rootPower] at hleftLeaf
      · exact ihLeft (depth := depth + 1) hleftValid hleftLeaf
        (fun childPower hchildPower => by
          have hheap : power < childPower :=
            hleftHeap childPower hchildPower
          omega)
        leaf hleaf
    · by_cases hrightLeaf : right.rootPower = none
      · cases right with
        | leaf length =>
          simp only [leavesWithDepth, List.mem_singleton] at hleaf
          subst leaf
          have hlog := PowerValid.nodePower_lt_logb
            ⟨hbase, hwithin, hleftValid, hrightValid, hinput, hpower,
              hleftHeap, hrightHeap⟩
            hrightValid.2.2
            (show length ≤ left.totalLength + length by omega)
          norm_num only [Prod.fst, Prod.snd]
          exact le_trans (by exact_mod_cast hrootDepth) hlog.le
        | merge childPower childLeft childRight =>
          simp [rootPower] at hrightLeaf
      · exact ihRight (depth := depth + 1) hrightValid hrightLeaf
        (fun childPower hchildPower => by
          have hheap : power < childPower :=
            hrightHeap childPower hchildPower
          omega)
        leaf hleaf

end CPythonListsort.MergeTree

namespace CPythonListsort.MergeTree

/--
[PowerValid.leaf_depth_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerTreeEntropy.lean)
-/
@[path]
lemma PowerValid.leaf_depth_bound
  {listBase : Nat}
  {listLength : PySSize}
  {tree : MergeTree}
-- given
  (hvalid : tree.PowerValid listBase listLength listBase)
  (htotal : tree.totalLength = listLength.toNat) :
-- imply
  ∀ leaf ∈ tree.leavesWithDepth 0, (leaf.2 : Real) ≤ Real.logb 2 ((listLength.toNat : Real) / (leaf.1 : Real)) + 2 := by
-- proof
  cases tree with
  | leaf length =>
    intro leaf hleaf
    simp only [leavesWithDepth, List.mem_singleton] at hleaf
    subst leaf
    simp only [totalLength] at htotal
    have hlength : 0 < length := hvalid.2.2
    have hratio : ((listLength.toNat : Real) / (length : Real)) = 1 := by
      rw [← htotal]
      field_simp
    simp [hratio]
  | merge power left right =>
    have hrootPower : 1 ≤ power := by
      have hrange := powerRange
        (BitVec.ofNat 64 (listBase - listBase))
        (BitVec.ofNat 64 left.totalLength)
        (BitVec.ofNat 64 right.totalLength)
        listLength hvalid.2.2.2.2.1
      simpa only [hvalid.2.2.2.2.2.1] using hrange.1
    apply PowerValid.internal_leaf_depth_bound hvalid
    · simp [rootPower]
    · intro candidatePower hroot
      simp only [rootPower, Option.some.injEq] at hroot
      subst candidatePower
      exact hrootPower

end CPythonListsort.MergeTree

namespace CPythonListsort

/--
[powerMergePlanValid_empty_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerTreeEntropy.lean)
-/
@[path]
lemma powerMergePlanValid_empty_iff
  {listBase : Nat}
  {listLength : PySSize} :
-- imply
  PowerMergePlanValid listBase listLength .empty ↔ listLength.toNat = 0 := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[powerMergePlanValid_singleton_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerTreeEntropy.lean)
-/
@[path]
lemma powerMergePlanValid_singleton_iff
  {listBase length : Nat}
  {listLength : PySSize} :
-- imply
  PowerMergePlanValid listBase listLength (.tree (.leaf length)) ↔ length = listLength.toNat ∧ 0 < length := by
-- proof
  simp only [PowerMergePlanValid, MergeTree.PowerValid,
    MergeTree.totalLength]
  constructor
  · rintro ⟨⟨_, _, hpositive⟩, hlength⟩
    exact ⟨hlength, hpositive⟩
  · rintro ⟨hlength, hpositive⟩
    subst length
    omega

end CPythonListsort

namespace CPythonListsort

/--
[PowerMergePlanValid.mergeCost_le_entropy_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerTreeEntropy.lean)
-/
@[path]
lemma PowerMergePlanValid.mergeCost_le_entropy_add_two
  {listBase : Nat}
  {listLength : PySSize}
  {plan : MergePlan}
-- given
  (hvalid : PowerMergePlanValid listBase listLength plan) :
-- imply
  (plan.mergeCost : Real) ≤ (listLength.toNat : Real) * hvalid.runProfile.entropy + 2 * (listLength.toNat : Real) := by
-- proof
  apply plan.mergeCost_le_entropy_add_two hvalid.runProfile rfl
  cases plan with
  | empty => simp [MergePlan.leavesWithDepth]
  | tree root =>
    simpa [MergePlan.leavesWithDepth] using
      hvalid.1.leaf_depth_bound hvalid.2

end CPythonListsort

namespace CPythonListsort

/--
[PowerMergePlanValid.mergeCost_le_entropy_add_two_of_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerTreeEntropy.lean)
-/
@[path]
lemma PowerMergePlanValid.mergeCost_le_entropy_add_two_of_profile
  {listBase : Nat}
  {listLength : PySSize}
  {plan : MergePlan}
  {profile : RunProfile listLength.toNat}
-- given
  (hvalid : PowerMergePlanValid listBase listLength plan)
  (hlengths : plan.runLengths = profile.lengths) :
-- imply
  (plan.mergeCost : Real) ≤ (listLength.toNat : Real) * profile.entropy + 2 * (listLength.toNat : Real) := by
-- proof
  apply plan.mergeCost_le_entropy_add_two profile hlengths
  cases plan with
  | empty => simp [MergePlan.leavesWithDepth]
  | tree root =>
    simpa [MergePlan.leavesWithDepth] using
      hvalid.1.leaf_depth_bound hvalid.2

end CPythonListsort

namespace CPythonListsort

/--
[PowerMergePlanValid.mergeCost_le_entropy_mul_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerTreeEntropy.lean)
-/
@[path]
lemma PowerMergePlanValid.mergeCost_le_entropy_mul_add_two
  {listBase : Nat}
  {listLength : PySSize}
  {plan : MergePlan}
-- given
  (hvalid : PowerMergePlanValid listBase listLength plan) :
-- imply
  (plan.mergeCost : Real) ≤ hvalid.runProfile.entropy * (listLength.toNat : Real) + 2 * (listLength.toNat : Real) := by
-- proof
  simpa only [mul_comm] using hvalid.mergeCost_le_entropy_add_two

end CPythonListsort


-- created on 2026-10-23
