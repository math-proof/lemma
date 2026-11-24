module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.CPythonListsort.Code.Policy.PendingLayout
public import Def.CPythonListsort.Code.Policy.StackPowers
public import Def.CPythonListsort.Code.Policy.BoundaryPowerGeometry
public import Theorem.List.Atlas.CPythonListsort.Code.Policy.BoundaryPowerGeometry
public import Def.CPythonListsort.Code.Equivalence.PowerloopResults.Part2
public import Structure.CPythonListsort.Code.Transcription.MergeAt
public import Def.CPythonListsort.Code.Transcription.MergeAt.Part3
public import Theorem.CPythonListsort.Code.Transcription.FoundNewRun
public import Theorem.List.Atlas.CPythonListsort.Code.Policy.PendingLayout
public import Theorem.List.Atlas.CPythonListsort.Code.Transcription.MergeAt

public section



namespace CPythonListsort

/-- Empty power list is increasing. -/
public lemma increasingPendingPowers_nil :
    IncreasingPendingPowers [] :=
  ⟨[], rfl, by simp, by simp⟩

public lemma ExactBoundaryPowers.head
    {basekeys : Nat} {listlen : PySSize}
    {left right : PendingRun} {rest : List PendingRun}
    (h : ExactBoundaryPowers basekeys listlen (left :: right :: rest)) :
    left.power = some (pendingBoundaryPower basekeys listlen left right) :=
  h.1

public lemma ExactBoundaryPowers.tail
    {basekeys : Nat} {listlen : PySSize}
    {head : PendingRun} {tail : List PendingRun}
    (h : ExactBoundaryPowers basekeys listlen (head :: tail)) :
    ExactBoundaryPowers basekeys listlen tail := by
  cases tail with
  | nil => simp [ExactBoundaryPowers]
  | cons next rest => exact h.2

public lemma ExactBoundaryPowers.pair_of_append
    {basekeys : Nat} {listlen : PySSize}
    {before after : List PendingRun}
    {left right : PendingRun}
    (h : ExactBoundaryPowers basekeys listlen
      (before ++ left :: right :: after)) :
    left.power = some (pendingBoundaryPower basekeys listlen left right) := by
  induction before with
  | nil => exact h.head
  | cons _head before ih => exact ih h.tail

public lemma PoweredPrefix.exact_boundary_powers
    {κ : Type u} {ν : Type v} {state : MergeState κ ν}
    (h : PoweredPrefix state) :
    ExactBoundaryPowers state.basekeys state.listlen state.pending.toList := by
  obtain hempty | ⟨_, _, _, _, hexact⟩ := h
  · simp [hempty, ExactBoundaryPowers]
  · exact hexact

public lemma PoweredPrefix.boundary_power
    {κ : Type u} {ν : Type v} {state : MergeState κ ν}
    {before after : List PendingRun} {left right : PendingRun}
    (h : PoweredPrefix state)
    (hsplit : state.pending.toList = before ++ left :: right :: after) :
    left.power =
      some (pendingBoundaryPower state.basekeys state.listlen left right) := by
  apply ExactBoundaryPowers.pair_of_append
  simpa [hsplit] using h.exact_boundary_powers

end CPythonListsort



namespace CPythonListsort

/--
[pendingBoundaryPower_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeTopPowerPreservation.lean)
-/
@[path]
public lemma pendingBoundaryPower_geometry
  (basekeys : Nat)
  (listlen : PySSize)
  (left middle right : PendingRun)
-- given
  (hlistNonnegative : listlen.Nonnegative)
  (hlistMax : listlen.toNat ≤ PY_LIST_MAX)
  (hbase : basekeys ≤ left.base)
  (hleftMiddle : left.endIndex = middle.base)
  (hmiddleRight : middle.endIndex = right.base)
  (hleftPositive : 0 < left.len.toNat)
  (hmiddlePositive : 0 < middle.len.toNat)
  (hrightPositive : 0 < right.len.toNat)
  (hrightFits : right.endIndex ≤ basekeys + listlen.toNat) :
-- imply
  let pLM := pendingBoundaryPower basekeys listlen left middle
  let pMR := pendingBoundaryPower basekeys listlen middle right
  pLM ≠ pMR ∧
    (pLM < pMR →
      pendingBoundaryPower basekeys listlen left
        { middle with len := middle.len + right.len } = pLM) ∧
    (pMR < pLM →
      pendingBoundaryPower basekeys listlen
        { left with len := left.len + middle.len } right = pMR) := by
-- proof
  dsimp only
  let s := left.base - basekeys
  let a := left.len.toNat
  let b := middle.len.toNat
  let c := right.len.toNat
  let n := listlen.toNat
  have hleftBase : left.base = basekeys + s := by
    dsimp [s]
    omega
  have hmiddleBase : middle.base = basekeys + s + a := by
    rw [← hleftMiddle]
    simp only [PendingRun.endIndex]
    dsimp [a]
    omega
  have hmiddleOffset : middle.base - basekeys = s + a := by
    rw [hmiddleBase]
    omega
  have hrightBase : right.base = basekeys + s + a + b := by
    rw [← hmiddleRight]
    simp only [PendingRun.endIndex]
    dsimp [b]
    omega
  have hfits : s + a + b + c ≤ n := by
    simp only [PendingRun.endIndex] at hrightFits
    dsimp [s, a, b, c, n]
    omega
  have hgeometry := boundaryPowerGeometry (s := s) (a := a) (b := b) (c := c) (n := n)
    (by simpa [a] using hleftPositive)
    (by simpa [b] using hmiddlePositive)
    (by simpa [c] using hrightPositive)
    hfits (by simpa [n] using hlistMax)
  have hleftLen : BitVec.ofNat 64 a = left.len := by
    apply BitVec.toNat_injective
    simp [a]
  have hmiddleLen : BitVec.ofNat 64 b = middle.len := by
    apply BitVec.toNat_injective
    simp [b]
  have hrightLen : BitVec.ofNat 64 c = right.len := by
    apply BitVec.toNat_injective
    simp [c]
  have hlistlen : BitVec.ofNat 64 n = listlen := by
    apply BitVec.toNat_injective
    simp [n]
  have hmiddleRightSum :
    BitVec.ofNat 64 (b + c) = middle.len + right.len := by
    apply BitVec.toNat_injective
    have hsumLt : middle.len.toNat + right.len.toNat < 2 ^ 64 := by
      have hlistLt : listlen.toNat < 2 ^ 63 := by
        rw [PySSize.Nonnegative, BitVec.msb_eq_false_iff_two_mul_lt]
          at hlistNonnegative
        norm_num at hlistNonnegative ⊢
        omega
      dsimp [b, c]
      omega
    have hsumLt' :
      middle.len.toNat + right.len.toNat < 18446744073709551616 := by
      norm_num at hsumLt ⊢
      exact hsumLt
    rw [BitVec.toNat_add_of_lt (w := 64) (x := middle.len)
      (y := right.len) hsumLt']
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simpa [b, c] using hsumLt)]
  have hleftMiddleSum :
    BitVec.ofNat 64 (a + b) = left.len + middle.len := by
    apply BitVec.toNat_injective
    have hsumLt : left.len.toNat + middle.len.toNat < 2 ^ 64 := by
      have hlistLt : listlen.toNat < 2 ^ 63 := by
        rw [PySSize.Nonnegative, BitVec.msb_eq_false_iff_two_mul_lt]
          at hlistNonnegative
        norm_num at hlistNonnegative ⊢
        omega
      dsimp [a, b]
      omega
    have hsumLt' :
      left.len.toNat + middle.len.toNat < 18446744073709551616 := by
      norm_num at hsumLt ⊢
      exact hsumLt
    rw [BitVec.toNat_add_of_lt (w := 64) (x := left.len)
      (y := middle.len) hsumLt']
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simpa [a, b] using hsumLt)]
  simpa [pendingBoundaryPower, s, a, b, c, n, hleftLen, hmiddleLen,
    hrightLen, hlistlen, hmiddleRightSum, hleftMiddleSum, hmiddleOffset,
    hrightBase]
    using hgeometry

end CPythonListsort

namespace CPythonListsort

/--
[IncreasingPendingPowers.prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeTopPowerPreservation.lean)
-/
@[path]
public lemma IncreasingPendingPowers.prefix
  {runs suffix : List PendingRun}
-- given
  (h : IncreasingPendingPowers (runs ++ suffix)) :
-- imply
  IncreasingPendingPowers runs := by
-- proof
  obtain ⟨powers, hmap, hrange, hstrict⟩ := h
  let prefixPowers := powers.take runs.length
  refine ⟨prefixPowers, ?_, ?_, ?_⟩
  · have htake := congrArg (List.take runs.length) hmap
    simpa [prefixPowers] using htake
  · intro power hpower
    exact hrange power (List.take_subset runs.length powers hpower)
  · exact List.Pairwise.sublist (List.take_sublist runs.length powers) hstrict

end CPythonListsort

namespace CPythonListsort

/--
[PoweredPrefix.increasing_of_eq_snoc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeTopPowerPreservation.lean)
-/
@[path]
public lemma PoweredPrefix.increasing_of_eq_snoc
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {older : List PendingRun}
  {newest : PendingRun}
-- given
  (h : PoweredPrefix state)
  (hsplit : state.pending.toList = older ++ [newest]) :
-- imply
  IncreasingPendingPowers older := by
-- proof
  obtain hempty | ⟨actualOlder, actualNewest, hactual, hpowers, _⟩ := h
  · rw [hempty] at hsplit
    have : (older ++ [newest]).length = 0 := by simpa using congrArg List.length hsplit.symm
    simp at this
  · have heq : older ++ [newest] = actualOlder ++ [actualNewest] :=
    hsplit.symm.trans hactual
    have hlength : older.length = actualOlder.length := by
      have := congrArg List.length heq
      simp only [List.length_append, List.length_singleton] at this
      omega
    have hparts := List.append_inj heq hlength
    simpa [hparts.1] using hpowers

end CPythonListsort

namespace CPythonListsort

/--
[increasingPowers_lt_last_aux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeTopPowerPreservation.lean)
-/
@[path]
private theorem increasingPowers_lt_last_aux
  (runs : List PendingRun) (last : PendingRun) (powers : List Nat)
  (p : Nat)
  (hmap : (runs ++ [last]).map PendingRun.power = powers.map some)
  (hstrict : powers.Pairwise (fun x y => x < y))
  (hlast : last.power = some p) :
  ∀ run ∈ runs, ∀ q, run.power = some q → q < p := by
  induction runs generalizing powers with
  | nil => simp
  | cons head runs ih =>
    cases powers with
    | nil => simp at hmap
    | cons headPower tailPowers =>
      simp only [List.cons_append, List.map_cons, List.cons.injEq] at hmap
      obtain ⟨hhead, htail⟩ := hmap
      simp only [List.pairwise_cons] at hstrict
      obtain ⟨hheadLt, htailStrict⟩ := hstrict
      intro run hrun q hrunPower
      simp only [List.mem_cons] at hrun
      obtain rfl | hrun := hrun
      · have hq : q = headPower := by
          rw [hrunPower] at hhead
          exact Option.some.inj hhead
        subst q
        have hpMem : p ∈ tailPowers := by
          have hsomeMem : some p ∈ tailPowers.map some := by
            rw [← htail]
            simp [hlast]
          simpa using hsomeMem
        exact hheadLt p hpMem
      · exact ih tailPowers htail htailStrict run hrun q hrunPower

end CPythonListsort

namespace CPythonListsort

/--
[IncreasingPendingPowers.power_lt_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeTopPowerPreservation.lean)
-/
@[path]
public lemma IncreasingPendingPowers.power_lt_last
  {runs : List PendingRun}
  {last run : PendingRun}
  {p q : Nat}
-- given
  (h : IncreasingPendingPowers (runs ++ [last]))
  (hrun : run ∈ runs)
  (hrunPower : run.power = some q)
  (hlastPower : last.power = some p) :
-- imply
  q < p := by
-- proof
  obtain ⟨powers, hmap, _, hstrict⟩ := h
  exact increasingPowers_lt_last_aux runs last powers p hmap hstrict hlastPower
    run hrun q hrunPower

end CPythonListsort

namespace CPythonListsort

/--
[ExactBoundaryPowers.replace_last_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeTopPowerPreservation.lean)
-/
@[path]
public lemma ExactBoundaryPowers.replace_last_boundary
  {basekeys : Nat}
  {listlen : PySSize}
  {before : List PendingRun}
  {previous left right : PendingRun}
-- given
  (h : ExactBoundaryPowers basekeys listlen (before ++ [previous, left, right]))
  (hnew : previous.power = some (pendingBoundaryPower basekeys listlen previous { left with len := left.len + right.len })) :
-- imply
  ExactBoundaryPowers basekeys listlen (before ++ [previous, { left with len := left.len + right.len }]) := by
-- proof
  induction before with
  | nil => simpa [ExactBoundaryPowers] using hnew
  | cons head before ih =>
    cases before <;>
      simp only [List.cons_append, List.nil_append, ExactBoundaryPowers] at h ⊢
    all_goals exact ⟨h.1, ih h.2⟩

end CPythonListsort

namespace CPythonListsort

/--
[PendingRunsCover.member_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeTopPowerPreservation.lean)
-/
@[path]
public lemma PendingRunsCover.member_spec
  {cursor limit : Nat}
  {runs : List PendingRun}
  {run : PendingRun}
-- given
  (h : PendingRunsCover cursor limit runs)
  (hrun : run ∈ runs) :
-- imply
  cursor ≤ run.base ∧ run.len.Nonnegative ∧ 0 < run.len.toNat ∧ run.endIndex ≤ limit := by
-- proof
  induction runs generalizing cursor with
  | nil => simp at hrun
  | cons head runs ih =>
    simp only [PendingRunsCover] at h
    obtain ⟨hbase, hnonnegative, hpositive, hend, htail⟩ := h
    simp only [List.mem_cons] at hrun
    obtain rfl | hrun := hrun
    · exact ⟨by omega, hnonnegative, hpositive, hend⟩
    · rcases ih htail hrun with ⟨hlower, hrnn, hrpos, hrend⟩
      have hheadEnd : cursor < head.endIndex := by
        simp only [PendingRun.endIndex]
        omega
      exact ⟨by omega, hrnn, hrpos, hrend⟩

end CPythonListsort

namespace CPythonListsort

/--
[PendingRunsCover.last_end_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeTopPowerPreservation.lean)
-/
@[path]
public lemma PendingRunsCover.last_end_eq
  {cursor limit : Nat}
  {before : List PendingRun}
  {last : PendingRun}
-- given
  (h : PendingRunsCover cursor limit (before ++ [last])) :
-- imply
  last.endIndex = limit := by
-- proof
  induction before generalizing cursor with
  | nil =>
    simpa [PendingRunsCover] using h.2.2.2.2
  | cons head before ih =>
    simp only [List.cons_append, PendingRunsCover] at h
    exact ih h.2.2.2.2

end CPythonListsort

namespace CPythonListsort

/--
[PendingRunsCover.mergeAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeAtPreservation.lean)
-/
@[path]
public lemma PendingRunsCover.mergeAdjacent
  {cursor limit : Nat}
  {before after : List PendingRun}
  {left right : PendingRun}
-- given
  (hcover : PendingRunsCover cursor limit (before ++ left :: right :: after))
  (hfit : left.len.toNat + right.len.toNat < 2 ^ 63) :
-- imply
  PendingRunsCover cursor limit (before ++ ({ left with len := left.len + right.len } : PendingRun) :: after) := by
-- proof
  have hfit64 : left.len.toNat + right.len.toNat < 2 ^ 64 := by
    norm_num at hfit ⊢
    omega
  have hsum :
    (left.len + right.len).toNat =
      left.len.toNat + right.len.toNat :=
    BitVec.toNat_add_of_lt hfit64
  have hnonnegative : (left.len + right.len).Nonnegative := by
    rw [PySSize.Nonnegative, BitVec.msb_eq_false_iff_two_mul_lt, hsum]
    norm_num at hfit ⊢
    omega
  induction before generalizing cursor with
  | nil =>
    simp only [List.nil_append, PendingRunsCover] at hcover ⊢
    rcases hcover with
      ⟨hleftBase, hleftNonnegative, hleftPositive, _, hrightBase,
        _, hrightPositive, hrightEnd, hafter⟩
    have hend :
      ({ left with len := left.len + right.len } : PendingRun).endIndex =
        right.endIndex := by
      simp only [PendingRun.endIndex]
      simp only [hsum]
      rw [hrightBase]
      simp only [PendingRun.endIndex]
      omega
    exact
      ⟨hleftBase, hnonnegative, by simp only [hsum]; omega,
        hend.le.trans hrightEnd, hend.symm ▸ hafter⟩
  | cons run before ih =>
    simp only [List.cons_append, PendingRunsCover] at hcover ⊢
    exact
      ⟨hcover.1, hcover.2.1, hcover.2.2.1, hcover.2.2.2.1,
        ih hcover.2.2.2.2⟩

end CPythonListsort

namespace CPythonListsort

/--
[PendingRunsCover.pair_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeAtPreservation.lean)
-/
@[path]
public lemma PendingRunsCover.pair_spec
  {cursor limit : Nat}
  {before after : List PendingRun}
  {left right : PendingRun}
-- given
  (hcover : PendingRunsCover cursor limit (before ++ left :: right :: after)) :
-- imply
  left.len.Nonnegative ∧ 0 < left.len.toNat ∧ right.len.Nonnegative ∧ 0 < right.len.toNat ∧ left.endIndex = right.base := by
-- proof
  induction before generalizing cursor with
  | nil =>
    simp only [List.nil_append, PendingRunsCover] at hcover
    rcases hcover with
      ⟨_, hleftNonnegative, hleftPositive, _, hrightBase,
        hrightNonnegative, hrightPositive, _, _⟩
    exact
      ⟨hleftNonnegative, hleftPositive, hrightNonnegative,
        hrightPositive, hrightBase.symm⟩
  | cons run before ih =>
    simp only [List.cons_append, PendingRunsCover] at hcover
    exact ih hcover.2.2.2.2

end CPythonListsort

namespace CPythonListsort

/--
[PendingLayout.pairFits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeAtPreservation.lean)
-/
@[path]
public lemma PendingLayout.pairFits
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {scanned : Nat}
  {before after : List PendingRun}
  {left right : PendingRun}
-- given
  (hlayout : PendingLayout state scanned)
  (hsplit : state.pending.toList = before ++ left :: right :: after) :
-- imply
  left.len.toNat + right.len.toNat < 2 ^ 63 := by
-- proof
  obtain ⟨hlistNonnegative, _, hscanned, hcover⟩ := hlayout
  have htotal := hcover.totalLength
  rw [hsplit] at htotal
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at htotal
  have hpairLe : left.len.toNat + right.len.toNat ≤ scanned := by
    omega
  have hlistLt : state.listlen.toNat < 2 ^ 63 := by
    rw [PySSize.Nonnegative, BitVec.msb_eq_false_iff_two_mul_lt] at hlistNonnegative
    norm_num at hlistNonnegative ⊢
    omega
  omega

end CPythonListsort

namespace CPythonListsort

/--
[Array.toList_set_eraseIdx_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeAtPreservation.lean)
-/
@[path]
public lemma Array.toList_set_eraseIdx_adjacent
  {α : Type u}
  {xs : Array α}
  {i : Nat}
  {before after : List α}
  {left right replacement : α}
-- given
  (hsplit : xs.toList = before ++ left :: right :: after)
  (hbefore : before.length = i) :
-- imply
  ((xs.setIfInBounds i replacement).eraseIdxIfInBounds (i + 1)).toList = before ++ replacement :: after := by
-- proof
  rw [Array.toList_eraseIdxIfInBounds, Array.toList_setIfInBounds]
  rw [hsplit]
  subst i
  rw [List.set_append_right before.length replacement (by omega)]
  simp only [Nat.sub_self, List.set_cons_zero]
  rw [List.eraseIdx_append_of_length_le (by omega)]
  simp

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[pendingLayout_after_mergeAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeAtPreservation.lean)
transport `PendingLayout`; merge data and comparator behavior are irrelevant.
-/
@[path]
private theorem pendingLayout_after_mergeAdjacent
  (state state' : MergeState κ ν) (scanned : Nat)
  (before after : List PendingRun) (left right : PendingRun)
  (hlayout : PendingLayout state scanned)
  (hsplit :
    state.pending.toList = before ++ left :: right :: after)
  (hlistlen : state'.listlen = state.listlen)
  (hbasekeys : state'.basekeys = state.basekeys)
  (hdataSize : state'.data.entries.size = state.data.entries.size)
  (hpending :
    state'.pending.toList =
      before ++
        ({ left with len := left.len + right.len } : PendingRun) :: after) :
  PendingLayout state' scanned := by
  obtain ⟨hlistNonnegative, hdataBound, hscanned, hcover⟩ := hlayout
  have hfit : left.len.toNat + right.len.toNat < 2 ^ 63 :=
    PendingLayout.pairFits
      ⟨hlistNonnegative, hdataBound, hscanned, hcover⟩ hsplit
  rw [hsplit] at hcover
  have hmerged := hcover.mergeAdjacent hfit
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hlistlen] using hlistNonnegative
  · simpa only [hbasekeys, hlistlen, hdataSize] using hdataBound
  · simpa only [hlistlen] using hscanned
  · simpa only [hbasekeys, hpending] using hmerged

end CPythonListsort


namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[setTopPower_pending_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/FoundNewRunPreservation.lean)
-/
@[path]
private theorem setTopPower_pending_frame
  (state state' : MergeState κ ν) (power : Nat)
  (before : List PendingRun) (top : PendingRun)
  (hsplit : state.pending.toList = before ++ [top])
  (hset : setTopPower? state power = some state') :
  state'.pending.toList =
    before ++ [{ top with power := some power }] ∧
    state'.listlen = state.listlen ∧
    state'.basekeys = state.basekeys ∧
    state'.data.entries.size = state.data.entries.size := by
  unfold setTopPower? at hset
  have hnonempty : state.pending.isEmpty = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hempty
    rw [Array.isEmpty_iff] at hempty
    have hlen := congrArg List.length hsplit
    rw [hempty] at hlen
    simp at hlen
  simp only [hnonempty, Bool.false_eq_true, ite_false] at hset
  have hsize : state.pending.size = before.length + 1 := by
    have hlen := congrArg List.length hsplit
    simpa using hlen
  have hlookup : state.pending[state.pending.size - 1]? = some top := by
    rw [← Array.getElem?_toList, hsplit, hsize]
    simp
  rw [hlookup] at hset
  injection hset with hstate'
  subst state'
  refine ⟨?_, rfl, rfl, rfl⟩
  rw [Array.toList_setIfInBounds, hsplit, hsize]
  simp

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[replace_last_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/FoundNewRunPreservation.lean)
interval cover.
-/
@[path]
private theorem PendingRunsCover.replace_last_power
  {cursor limit : Nat} {before : List PendingRun} {top : PendingRun}
  {power : Nat}
  (h : PendingRunsCover cursor limit (before ++ [top])) :
  PendingRunsCover cursor limit
    (before ++ [{ top with power := some power }]) := by
  induction before generalizing cursor with
  | nil => simpa [PendingRunsCover, PendingRun.endIndex] using h
  | cons head before ih =>
    simp only [List.cons_append, PendingRunsCover] at h ⊢
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ih h.2.2.2.2⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[set_last_and_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/FoundNewRunPreservation.lean)
prospective run establishes exact labels on the virtual post-push list.
-/
@[path]
private theorem ExactBoundaryPowers.set_last_and_append
  {basekeys : Nat} {listlen : PySSize}
  {before : List PendingRun} {top newRun : PendingRun} {power : Nat}
  (hexact : ExactBoundaryPowers basekeys listlen (before ++ [top]))
  (hpower : power = pendingBoundaryPower basekeys listlen top newRun) :
  ExactBoundaryPowers basekeys listlen
    (before ++ [{ top with power := some power }, newRun]) := by
  induction before with
  | nil =>
    simp only [List.nil_append, ExactBoundaryPowers]
    refine ⟨?_, trivial⟩
    simp [hpower, pendingBoundaryPower]
  | cons head before ih =>
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons_append, ExactBoundaryPowers]
        at hexact ⊢
      refine ⟨?_, ?_⟩
      · simpa [pendingBoundaryPower] using hexact.1
      · refine ⟨?_, trivial⟩
        simp [hpower, pendingBoundaryPower]
    | cons next rest =>
      simp only [List.cons_append, ExactBoundaryPowers] at hexact ⊢
      exact ⟨hexact.1, ih hexact.2⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[append_of_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/FoundNewRunPreservation.lean)
power list.
-/
@[path]
private theorem IncreasingPendingPowers.append_of_upper
  {runs : List PendingRun} {top : PendingRun} {power : Nat}
  (h : IncreasingPendingPowers runs)
  (hrange : 1 ≤ power ∧ power ≤ 60)
  (hupper : ∀ run ∈ runs, ∀ candidate,
    run.power = some candidate → candidate < power) :
  IncreasingPendingPowers
    (runs ++ [{ top with power := some power }]) := by
  obtain ⟨powers, hmap, hpowersRange, hstrict⟩ := h
  refine ⟨powers ++ [power], ?_, ?_, ?_⟩
  · simp only [List.map_append, List.map_singleton]
    rw [hmap]
  · intro candidate hcandidate
    simp only [List.mem_append, List.mem_singleton] at hcandidate
    obtain hcandidate | rfl := hcandidate
    · exact hpowersRange candidate hcandidate
    · exact hrange
  · rw [List.pairwise_append]
    refine ⟨hstrict, by simp, ?_⟩
    intro candidate hcandidate last hlast
    simp only [List.mem_singleton] at hlast
    subst last
    have hsomeMem : some candidate ∈ runs.map PendingRun.power := by
      rw [hmap]
      exact List.mem_map.mpr ⟨candidate, hcandidate, rfl⟩
    obtain ⟨run, hrun, hrunPower⟩ := List.mem_map.mp hsomeMem
    exact hupper run hrun candidate hrunPower

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[member_base_lt_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/FoundNewRunPreservation.lean)
-/
@[path]
private theorem PendingRunsCover.member_base_lt_limit
  {cursor limit : Nat} {runs : List PendingRun} {run : PendingRun}
  (hcover : PendingRunsCover cursor limit runs) (hrun : run ∈ runs) :
  run.base < limit := by
  obtain ⟨_, _, hpositive, hend⟩ := hcover.member_spec hrun
  simp only [PendingRun.endIndex] at hend
  omega

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[newRun_not_mem_of_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/FoundNewRunPreservation.lean)
prefix.  This remains true after power-only updates.
-/
@[path]
private theorem newRun_not_mem_of_layout
  {state : MergeState κ ν} {scanned : Nat} {newRun : PendingRun}
  (hlayout : PendingLayout state scanned)
  (hnewBase : newRun.base = state.basekeys + scanned) :
  newRun ∉ state.pending.toList := by
  intro hmem
  have hlt := hlayout.2.2.2.member_base_lt_limit hmem
  rw [hnewBase] at hlt
  omega

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[setTopPower_establishes_ready](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/FoundNewRunPreservation.lean)
boundary power on the surviving top establishes the complete pre-push policy
postcondition.
-/
@[path]
private theorem setTopPower_establishes_ready
  (state state' : MergeState κ ν) (scanned : Nat)
  (before : List PendingRun) (top newRun : PendingRun) (power : Nat)
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hlayout : PendingLayout state scanned)
  (hpowered : PoweredPrefix state)
  (hsplit : state.pending.toList = before ++ [top])
  (hnewBase : newRun.base = state.basekeys + scanned)
  (hnewNonnegative : newRun.len.Nonnegative)
  (hnewPositive : 0 < newRun.len.toNat)
  (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
  (hpower : power =
    pendingBoundaryPower state.basekeys state.listlen top newRun)
  (hpowerRange : 1 ≤ power ∧ power ≤ 60)
  (hstop : before = [] ∨
    ∃ older preceding precedingPower,
      before = older ++ [preceding] ∧
        preceding.power = some precedingPower ∧
        ¬ power < precedingPower)
  (hset : setTopPower? state power = some state') :
  ReadyToPush state' scanned newRun := by
  rcases setTopPower_pending_frame state state' power before top hsplit hset with
    ⟨hresultPending, hlistlen, hbasekeys, hdataSize⟩
  have hresultLayout : PendingLayout state' scanned := by
    rcases hlayout with
      ⟨hlistNonnegative, hdataBound, hscanned, hcover⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hlistlen] using hlistNonnegative
    · rw [hbasekeys, hlistlen, hdataSize]
      exact hdataBound
    · simpa [hlistlen] using hscanned
    · rw [hresultPending, hbasekeys]
      exact PendingRunsCover.replace_last_power (by rwa [hsplit] at hcover)
  have hincreasingBefore : IncreasingPendingPowers before :=
    hpowered.increasing_of_eq_snoc hsplit
  have hupper : ∀ run ∈ before, ∀ candidate,
    run.power = some candidate → candidate < power := by
    obtain hbeforeEmpty | ⟨older, preceding, precedingPower, hbefore,
        hprecedingPower, hnotGuard⟩ := hstop
    · subst before
      simp
    · have hcover : PendingRunsCover state.basekeys
          (state.basekeys + scanned) (older ++ [preceding, top]) := by
        have := hlayout.2.2.2
        rw [hsplit, hbefore] at this
        simpa [List.append_assoc] using this
      have hprecedingSpec := hcover.member_spec
        (run := preceding) (by simp)
      have hprecedingTop := hcover.pair_spec
        (before := older) (after := [])
        (left := preceding) (right := top)
      have htopEnd : top.endIndex = state.basekeys + scanned := by
        apply PendingRunsCover.last_end_eq
          (before := older ++ [preceding]) (last := top)
        simpa [List.append_assoc] using hcover
      have htopNew : top.endIndex = newRun.base := by
        rw [hnewBase, htopEnd]
      have hnewEndFits :
        newRun.endIndex ≤ state.basekeys + state.listlen.toNat := by
        simp only [PendingRun.endIndex, hnewBase]
        omega
      have hgeometry := pendingBoundaryPower_geometry
        state.basekeys state.listlen preceding top newRun hlayout.1 hmax
        hprecedingSpec.1 hprecedingTop.2.2.2.2 htopNew
        hprecedingTop.2.1 hprecedingTop.2.2.2.1 hnewPositive
        hnewEndFits
      have hstoredExact : preceding.power = some
        (pendingBoundaryPower state.basekeys state.listlen preceding top) := by
        apply hpowered.boundary_power (before := older) (after := [])
        simpa [hbefore, List.append_assoc] using hsplit
      have hprecedingPowerEq : precedingPower =
        pendingBoundaryPower state.basekeys state.listlen preceding top := by
        rw [hprecedingPower] at hstoredExact
        exact Option.some.inj hstoredExact
      have hpqNe : precedingPower ≠ power := by
        simpa [hprecedingPowerEq, hpower] using hgeometry.1
      have hpq : precedingPower < power := by omega
      intro run hrun candidate hcandidate
      rw [hbefore] at hrun
      simp only [List.mem_append, List.mem_singleton] at hrun
      obtain hrun | rfl := hrun
      · have hbeforeIncreasing :
            IncreasingPendingPowers (older ++ [preceding]) := by
          simpa [hbefore] using hincreasingBefore
        exact (hbeforeIncreasing.power_lt_last hrun hcandidate
          hprecedingPower).trans hpq
      · rw [hcandidate] at hprecedingPower
        have : candidate = precedingPower := Option.some.inj hprecedingPower
        omega
  have hresultIncreasing :
    IncreasingPendingPowers state'.pending.toList := by
    rw [hresultPending]
    exact hincreasingBefore.append_of_upper hpowerRange hupper
  have hstateExact : ExactBoundaryPowers state.basekeys state.listlen
    (before ++ [top]) := by
    simpa [hsplit] using hpowered.exact_boundary_powers
  have hresultExact : ExactBoundaryPowers state'.basekeys state'.listlen
    (state'.pending.toList ++ [newRun]) := by
    rw [hresultPending, hbasekeys, hlistlen]
    simpa [List.append_assoc] using
      hstateExact.set_last_and_append hpower
  have hresultNewBase : newRun.base = state'.basekeys + scanned := by
    simpa [hbasekeys] using hnewBase
  refine ⟨hresultLayout, hresultIncreasing, hresultExact,
    hresultNewBase, hnewNonnegative, hnewPositive, ?_, ?_⟩
  · simpa [hlistlen] using hnewWithin
  · exact newRun_not_mem_of_layout hresultLayout hresultNewBase

end CPythonListsort

namespace CPythonListsort

/--
[mergeAt_preserves_pendingLayout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeAtPreservation.lean)
-/
@[path]
public lemma mergeAt_preserves_pendingLayout
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {scanned i : Nat}
  {result : MergeAtResult κ ν}
-- given
  (hlayout : PendingLayout state scanned)
  (hmerge : mergeAt? state i = some result) :
-- imply
  ∃ before left right after, before.length = i ∧ state.pending.toList = before ++ left :: right :: after ∧ result.state.pending.toList = before ++ ({ left with len := left.len + right.len } : PendingRun) :: after ∧ left.len.Nonnegative ∧ 0 < left.len.toNat ∧ right.len.Nonnegative ∧ 0 < right.len.toNat ∧ left.endIndex = right.base ∧ (left.len + right.len).toNat = left.len.toNat + right.len.toNat ∧ PendingLayout result.state scanned := by
-- proof
  rcases mergeAt_pending_frame_of_eq_some hmerge with
    ⟨left, right, hleft, hright, hlistlen, hbasekeys, hdataSize, hpending⟩
  rcases Array.exists_pair_split_of_getElem?_eq_some hleft hright with
    ⟨before, after, hbefore, hsplit⟩
  have hresultPending :
    result.state.pending.toList =
      before ++
        ({ left with len := left.len + right.len } : PendingRun) :: after := by
    calc
      result.state.pending.toList =
        ((state.pending.setIfInBounds i
          ({ left with len := left.len + right.len } : PendingRun))
          |>.eraseIdxIfInBounds (i + 1)).toList :=
        congrArg Array.toList hpending
      _ = before ++
        ({ left with len := left.len + right.len } : PendingRun) :: after :=
        Array.toList_set_eraseIdx_adjacent hsplit hbefore
  have hcover := hlayout.2.2.2
  rw [hsplit] at hcover
  rcases hcover.pair_spec with
    ⟨hleftNonnegative, hleftPositive, hrightNonnegative, hrightPositive,
      hadjacent⟩
  have hfit : left.len.toNat + right.len.toNat < 2 ^ 63 :=
    hlayout.pairFits hsplit
  have hfit64 : left.len.toNat + right.len.toNat < 2 ^ 64 := by
    norm_num at hfit ⊢
    omega
  have hsum :
    (left.len + right.len).toNat =
      left.len.toNat + right.len.toNat :=
    BitVec.toNat_add_of_lt hfit64
  refine
    ⟨before, left, right, after, hbefore, hsplit, hresultPending,
      hleftNonnegative, hleftPositive, hrightNonnegative, hrightPositive,
      hadjacent, hsum, ?_⟩
  exact pendingLayout_after_mergeAdjacent state result.state scanned
    before after left right hlayout hsplit hlistlen hbasekeys hdataSize
    hresultPending

end CPythonListsort

namespace CPythonListsort

/--
[mergeTop_preserves_poweredPrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeTopPowerPreservation.lean)
-/
@[path]
public lemma mergeTop_preserves_poweredPrefix
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {scanned : Nat}
  {before : List PendingRun}
  {left right newRun : PendingRun}
  {pInternal q : Nat}
  {result : MergeAtResult κ ν}
-- given
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hlayout : PendingLayout state scanned)
  (hpowered : PoweredPrefix state)
  (hsplit : state.pending.toList = before ++ [left, right])
  (hnewBase : newRun.base = state.basekeys + scanned)
  (_hnewNonnegative : newRun.len.Nonnegative)
  (hnewPositive : 0 < newRun.len.toNat)
  (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
  (_hnewOutside : newRun ∉ state.pending.toList)
  (hleftPower : left.power = some pInternal)
  (hpInternal : pInternal = pendingBoundaryPower state.basekeys state.listlen left right)
  (hq : q = pendingBoundaryPower state.basekeys state.listlen right newRun)
  (hguard : q < pInternal)
  (hmerge : mergeAt? state (state.pending.size - 2) = some result)
  (_hcode : result.returnCode = 0)
  (_hfuel : result.fuelExhausted = false) :
-- imply
  let merged : PendingRun := { left with len := left.len + right.len }
  result.state.pending.toList = before ++ [merged] ∧
    merged.power = some pInternal ∧
    PendingLayout result.state scanned ∧
    PoweredPrefix result.state ∧
    q = pendingBoundaryPower result.state.basekeys result.state.listlen
      merged newRun := by
-- proof
  dsimp only
  let merged : PendingRun := { left with len := left.len + right.len }
  have hindex : state.pending.size - 2 = before.length := by
    have hsize := congrArg List.length hsplit
    simp only [Array.length_toList, List.length_append, List.length_cons,
      List.length_nil] at hsize
    omega
  rcases mergeAt_pending_frame_of_eq_some hmerge with
    ⟨actualLeft, actualRight, hactualLeft, hactualRight,
      hlistlen, hbasekeys, _hdataSize, hpending⟩
  have hleftLookup :
    state.pending[state.pending.size - 2]? = some left := by
    rw [← Array.getElem?_toList, hsplit, hindex]
    simp
  have hrightLookup :
    state.pending[state.pending.size - 2 + 1]? = some right := by
    rw [← Array.getElem?_toList, hsplit, hindex]
    simp
  have hactualLeftEq : actualLeft = left := by
    rw [hleftLookup] at hactualLeft
    exact Option.some.inj hactualLeft.symm
  have hactualRightEq : actualRight = right := by
    rw [hrightLookup] at hactualRight
    exact Option.some.inj hactualRight.symm
  subst actualLeft
  subst actualRight
  have hresultPending : result.state.pending.toList = before ++ [merged] := by
    calc
      result.state.pending.toList =
        ((state.pending.setIfInBounds (state.pending.size - 2) merged)
          |>.eraseIdxIfInBounds (state.pending.size - 2 + 1)).toList := by
            exact congrArg Array.toList hpending
      _ = before ++ [merged] := by
        simpa [merged] using
          Array.toList_set_eraseIdx_adjacent hsplit hindex.symm
  have hresultLayout : PendingLayout result.state scanned := by
    rcases mergeAt_preserves_pendingLayout hlayout hmerge with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hresultLayout⟩
    exact hresultLayout
  have hcover : PendingRunsCover state.basekeys (state.basekeys + scanned)
    (before ++ [left, right]) := by
    simpa [hsplit] using hlayout.2.2.2
  have hleftSpec := hcover.member_spec
    (run := left) (by simp)
  have hrightSpec := hcover.member_spec
    (run := right) (by simp)
  have hpair := hcover.pair_spec
    (before := before) (after := []) (left := left) (right := right)
  rcases hpair with
    ⟨hleftNonnegative, hleftPositive, hrightNonnegative,
      hrightPositive, hleftRight⟩
  have hrightEnd : right.endIndex = state.basekeys + scanned := by
    apply PendingRunsCover.last_end_eq
      (before := before ++ [left]) (last := right)
    simpa [List.append_assoc] using hcover
  have hnewAdjacency : right.endIndex = newRun.base := by
    rw [hnewBase, hrightEnd]
  have hnewEndFits :
    newRun.endIndex ≤ state.basekeys + state.listlen.toNat := by
    simp only [PendingRun.endIndex, hnewBase]
    omega
  have hgeometryNew := pendingBoundaryPower_geometry
    state.basekeys state.listlen left right newRun hlayout.1 hmax
    hleftSpec.1 hleftRight hnewAdjacency hleftPositive hrightPositive
    hnewPositive hnewEndFits
  have hghostState :
    q = pendingBoundaryPower state.basekeys state.listlen merged newRun := by
    rw [hq]
    exact (hgeometryNew.2.2 (by simpa [hpInternal, hq] using hguard)).symm
  have hghostResult :
    q = pendingBoundaryPower result.state.basekeys result.state.listlen
      merged newRun := by
    simpa only [hbasekeys, hlistlen] using hghostState
  have hmergedPower : merged.power = some pInternal := by
    simpa [merged] using hleftPower
  have hincreasingWithLeft :
    IncreasingPendingPowers (before ++ [left]) := by
    apply hpowered.increasing_of_eq_snoc
    simpa [List.append_assoc] using hsplit
  have hincreasingBefore : IncreasingPendingPowers before := by
    exact hincreasingWithLeft.prefix
  have hresultPowered : PoweredPrefix result.state := by
    rw [PoweredPrefix]
    right
    refine ⟨before, merged, hresultPending, hincreasingBefore, ?_⟩
    obtain hbefore | ⟨older, previous, hbefore⟩ := List.eq_nil_or_concat' before
    · subst before
      rw [hresultPending, hbasekeys, hlistlen]
      simp [ExactBoundaryPowers]
    · subst before
      have hpreviousLabel : previous.power = some
        (pendingBoundaryPower state.basekeys state.listlen previous left) := by
        apply hpowered.boundary_power
        simpa [List.append_assoc] using hsplit
      have hpreviousLt :
        pendingBoundaryPower state.basekeys state.listlen previous left <
          pInternal := by
        exact IncreasingPendingPowers.power_lt_last
          (runs := older ++ [previous]) (last := left) (run := previous)
          (p := pInternal)
          (q := pendingBoundaryPower state.basekeys state.listlen previous left)
          hincreasingWithLeft (by simp) hpreviousLabel hleftPower
      have hcoverTriple : PendingRunsCover state.basekeys
        (state.basekeys + scanned)
        (older ++ [previous, left, right]) := by
        simpa [List.append_assoc] using hcover
      have hpreviousSpec := hcoverTriple.member_spec
        (run := previous) (by simp)
      have hpreviousLeft := PendingRunsCover.pair_spec
        (before := older) (after := [right])
        (left := previous) (right := left)
        (by simpa [List.append_assoc] using hcoverTriple)
      have hleftRight' := PendingRunsCover.pair_spec
        (before := older ++ [previous]) (after := [])
        (left := left) (right := right)
        (by simpa [List.append_assoc] using hcoverTriple)
      have hrightWithinList :
        right.endIndex ≤ state.basekeys + state.listlen.toNat := by
        exact hrightSpec.2.2.2.trans
          (Nat.add_le_add_left hlayout.2.2.1 state.basekeys)
      have hgeometryPrevious := pendingBoundaryPower_geometry
        state.basekeys state.listlen previous left right hlayout.1 hmax
        hpreviousSpec.1 hpreviousLeft.2.2.2.2 hleftRight'.2.2.2.2
        hpreviousLeft.2.1 hleftRight'.2.1 hleftRight'.2.2.2.1
        hrightWithinList
      have hnewPrevious : previous.power = some
        (pendingBoundaryPower state.basekeys state.listlen previous merged) := by
        rw [hpreviousLabel]
        exact congrArg some (hgeometryPrevious.2.1
          (by simpa [hpInternal] using hpreviousLt)).symm
      have hexactState := hpowered.exact_boundary_powers
      rw [hsplit] at hexactState
      have hexactState' : ExactBoundaryPowers state.basekeys state.listlen
        (older ++ [previous, left, right]) := by
        simpa [List.append_assoc] using hexactState
      have hexactResultState : ExactBoundaryPowers state.basekeys state.listlen
        (older ++ [previous, merged]) := by
        exact hexactState'.replace_last_boundary hnewPrevious
      rw [hresultPending, hbasekeys, hlistlen]
      simpa [List.append_assoc] using hexactResultState
  exact ⟨hresultPending, hmergedPower, hresultLayout, hresultPowered,
    hghostResult⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[foundNewRunLoop_preserves_ready](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/FoundNewRunPreservation.lean)
a fixed ghost boundary against `newRun`; after every strict top merge the
geometry lemma re-establishes that same equality for the merged top.
-/
@[path]
private theorem foundNewRunLoop_preserves_ready
  (fuel : Nat) (state : MergeState κ ν) (scanned : Nat)
  (before : List PendingRun) (top newRun : PendingRun) (power : Nat)
  (result : FoundNewRunResult κ ν)
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hlayout : PendingLayout state scanned)
  (hpowered : PoweredPrefix state)
  (hsplit : state.pending.toList = before ++ [top])
  (hnewBase : newRun.base = state.basekeys + scanned)
  (hnewNonnegative : newRun.len.Nonnegative)
  (hnewPositive : 0 < newRun.len.toNat)
  (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
  (hpower : power =
    pendingBoundaryPower state.basekeys state.listlen top newRun)
  (hpowerRange : 1 ≤ power ∧ power ≤ 60)
  (hloop : foundNewRunLoop? fuel state power = some result)
  (hcode : result.returnCode = 0)
  (hfuel : result.fuelExhausted = false) :
  ReadyToPush result.state scanned newRun := by
  induction fuel generalizing state before top result with
  | zero =>
    simp only [foundNewRunLoop?] at hloop
    injection hloop with hresult
    subst result
    change true = false at hfuel
    contradiction
  | succ remaining ih =>
    have hsize : state.pending.size = before.length + 1 := by
      have := congrArg List.length hsplit
      simpa using this
    by_cases hmany : 1 < state.pending.size
    · rcases List.eq_nil_or_concat' before with hbeforeEmpty |
      ⟨older, preceding, hbefore⟩
      · subst before
        simp at hsize
        omega
      · have hlookup :
            state.pending[state.pending.size - 2]? = some preceding := by
          have hidx : state.pending.size - 2 = older.length := by
            rw [hsize, hbefore]
            simp
          rw [← Array.getElem?_toList, hsplit, hbefore, hidx]
          simp
        have hprecedingPower : preceding.power = some
          (pendingBoundaryPower state.basekeys state.listlen preceding top) := by
          apply hpowered.boundary_power (before := older) (after := [])
          simpa [hbefore, List.append_assoc] using hsplit
        let precedingPower :=
          pendingBoundaryPower state.basekeys state.listlen preceding top
        by_cases hguard : power < precedingPower
        · have hloop' := hloop
          dsimp only [precedingPower] at hguard
          simp only [foundNewRunLoop?, hmany, ite_eq_left, hlookup,
            hprecedingPower] at hloop'
          rw [ite_eq_left hguard] at hloop'
          cases hmergeOpt : mergeAt? state (state.pending.size - 2) with
          | none => simp [hmergeOpt] at hloop'
          | some merged =>
            simp only [hmergeOpt] at hloop'
            by_cases hmergeSuccess :
              merged.returnCode = 0 ∧ !merged.fuelExhausted
            · rw [ite_eq_left hmergeSuccess] at hloop'
              have hmergedFuel : merged.fuelExhausted = false := by
                simpa using hmergeSuccess.2
              have houtside : newRun ∉ state.pending.toList :=
                newRun_not_mem_of_layout hlayout hnewBase
              have hpolicy := mergeTop_preserves_poweredPrefix
                hmax hlayout hpowered
                (by simpa [hbefore, List.append_assoc] using hsplit)
                hnewBase hnewNonnegative hnewPositive hnewWithin houtside
                hprecedingPower rfl hpower hguard hmergeOpt
                hmergeSuccess.1 hmergedFuel
              let mergedTop : PendingRun :=
                { preceding with len := preceding.len + top.len }
              have hmergedSplit : merged.state.pending.toList =
                older ++ [mergedTop] := by
                simpa [mergedTop] using hpolicy.1
              have hmergedLayout : PendingLayout merged.state scanned :=
                hpolicy.2.2.1
              have hmergedPowered : PoweredPrefix merged.state :=
                hpolicy.2.2.2.1
              have hmergedPower : power = pendingBoundaryPower
                merged.state.basekeys merged.state.listlen mergedTop newRun := by
                simpa [mergedTop] using hpolicy.2.2.2.2
              rcases mergeAt_pending_frame_of_eq_some hmergeOpt with
                ⟨_, _, _, _, hmergedListlen, hmergedBasekeys, _, _⟩
              have hmergedMax :
                merged.state.listlen.toNat ≤ PY_LIST_MAX := by
                simpa [hmergedListlen] using hmax
              have hmergedNewBase :
                newRun.base = merged.state.basekeys + scanned := by
                simpa [hmergedBasekeys] using hnewBase
              have hmergedNewWithin :
                scanned + newRun.len.toNat ≤
                  merged.state.listlen.toNat := by
                simpa [hmergedListlen] using hnewWithin
              exact ih merged.state older mergedTop result hmergedMax
                hmergedLayout hmergedPowered hmergedSplit hmergedNewBase
                hmergedNewWithin hmergedPower hloop' hcode hfuel
            · rw [ite_eq_right hmergeSuccess] at hloop'
              injection hloop' with hresult
              subst result
              change merged.returnCode = 0 at hcode
              change merged.fuelExhausted = false at hfuel
              exfalso
              apply hmergeSuccess
              constructor
              · exact hcode
              · simp [hfuel]
        · have hloop' := hloop
          dsimp only [precedingPower] at hguard
          simp only [foundNewRunLoop?, hmany, ite_eq_left, hlookup,
            hprecedingPower] at hloop'
          rw [ite_eq_right hguard] at hloop'
          cases hsetOpt : setTopPower? state power with
          | none => simp [hsetOpt] at hloop'
          | some state' =>
            rw [hsetOpt] at hloop'
            injection hloop' with hresult
            subst result
            change ReadyToPush state' scanned newRun
            apply setTopPower_establishes_ready state state' scanned before
              top newRun power hmax hlayout hpowered hsplit hnewBase
              hnewNonnegative hnewPositive hnewWithin hpower hpowerRange
            · right
              exact ⟨older, preceding, precedingPower, hbefore,
                hprecedingPower, hguard⟩
            · exact hsetOpt
    · have hbeforeEmpty : before = [] := by
        have hlength : before.length = 0 := by omega
        exact List.eq_nil_of_length_eq_zero hlength
      have hloop' := hloop
      simp only [foundNewRunLoop?, hmany, ite_false] at hloop'
      cases hsetOpt : setTopPower? state power with
      | none => simp [hsetOpt] at hloop'
      | some state' =>
        rw [hsetOpt] at hloop'
        injection hloop' with hresult
        subst result
        change ReadyToPush state' scanned newRun
        apply setTopPower_establishes_ready state state' scanned before top
          newRun power hmax hlayout hpowered hsplit hnewBase
          hnewNonnegative hnewPositive hnewWithin hpower hpowerRange
        · exact Or.inl hbeforeEmpty
        · exact hsetOpt

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRun_preserves_readyToPush](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/FoundNewRunPreservation.lean)
-/
@[path]
public lemma foundNewRun_preserves_readyToPush
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {scanned : Nat}
  {newRun : PendingRun}
  {result : FoundNewRunResult κ ν}
-- given
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hlayout : PendingLayout state scanned)
  (hpowered : PoweredPrefix state)
  (hnewBase : newRun.base = state.basekeys + scanned)
  (hnewNonnegative : newRun.len.Nonnegative)
  (hnewPositive : 0 < newRun.len.toNat)
  (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
  (_hnewOutside : newRun ∉ state.pending.toList)
  (hfound : foundNewRun? state newRun.len.toNat = some result)
  (hcode : result.returnCode = 0)
  (hfuel : result.fuelExhausted = false) :
-- imply
  ReadyToPush result.state scanned newRun := by
-- proof
  by_cases hempty : state.pending.isEmpty = true
  · unfold foundNewRun? at hfound
    simp only [hempty, ite_eq_left] at hfound
    injection hfound with hresult
    subst result
    change ReadyToPush state scanned newRun
    have hpending : state.pending.toList = [] := by
      rw [Array.isEmpty_iff] at hempty
      simp [hempty]
    refine ⟨hlayout, ?_, ?_, hnewBase, hnewNonnegative, hnewPositive,
      hnewWithin, ?_⟩
    · rw [hpending]
      exact increasingPendingPowers_nil
    · simp [hpending, ExactBoundaryPowers]
    · simp [hpending]
  · have hnonempty : state.pending.toList ≠ [] := by
      intro hpending
      apply hempty
      rw [Array.isEmpty_iff_size_eq_zero]
      have hlength := congrArg List.length hpending
      simpa using hlength
    obtain hpending | ⟨before, top, hsplit⟩ :=
      List.eq_nil_or_concat' state.pending.toList
    · exact (hnonempty hpending).elim
    · have htopLookup :
          state.pending[state.pending.size - 1]? = some top := by
        have hsize : state.pending.size = before.length + 1 := by
          have := congrArg List.length hsplit
          simpa using this
        rw [← Array.getElem?_toList, hsplit, hsize]
        simp
      have hcover : PendingRunsCover state.basekeys
        (state.basekeys + scanned) (before ++ [top]) := by
        simpa [hsplit] using hlayout.2.2.2
      have htopSpec := hcover.member_spec (run := top) (by simp)
      have htopEnd : top.endIndex = state.basekeys + scanned := by
        exact PendingRunsCover.last_end_eq hcover
      have hfits : top.base - state.basekeys + top.len.toNat +
        newRun.len.toNat ≤ state.listlen.toNat := by
        simp only [PendingRun.endIndex] at htopEnd
        omega
      have hvalidNat := validPowerloopInput_ofNat
        (s := top.base - state.basekeys) (u := top.len.toNat)
        (v := newRun.len.toNat) (n := state.listlen.toNat)
        htopSpec.2.2.1 hnewPositive hfits hmax
      have htopLen : BitVec.ofNat 64 top.len.toNat = top.len := by
        simp
      have hnewLen : BitVec.ofNat 64 newRun.len.toNat = newRun.len := by
        simp
      have hlistlen : BitVec.ofNat 64 state.listlen.toNat = state.listlen := by
        simp
      have hvalid : ValidPowerloopInput
        (BitVec.ofNat 64 (top.base - state.basekeys)) top.len newRun.len
        state.listlen := by
        simpa [htopLen, hnewLen, hlistlen] using hvalidNat
      let prospectivePower :=
        (powerloopTraced
          (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
          newRun.len state.listlen).result
      have hprospectivePower : prospectivePower =
        pendingBoundaryPower state.basekeys state.listlen top newRun := by
        rfl
      have hpowerRangeRaw := powerRange
        (BitVec.ofNat 64 (top.base - state.basekeys)) top.len newRun.len
        state.listlen hvalid
      have hpowerRange :
        1 ≤ prospectivePower ∧ prospectivePower ≤ 60 := by
        simpa [prospectivePower, powerloop, POWER_BOUND, hnewLen] using
          ⟨hpowerRangeRaw.1, hpowerRangeRaw.2.1⟩
      have hstopped := (powerloopTraceSafety
        (BitVec.ofNat 64 (top.base - state.basekeys)) top.len newRun.len
        state.listlen hvalid).2
      unfold foundNewRun? at hfound
      have hnotEmptyBool : state.pending.isEmpty = false :=
        Bool.eq_false_of_not_eq_true hempty
      simp only [hnotEmptyBool, Bool.false_eq_true, ite_false, htopLookup]
        at hfound
      split at hfound
      next hguard =>
        simp only [hnewLen, hstopped, Bool.not_true, Bool.false_eq_true,
          ite_false] at hfound
        apply foundNewRunLoop_preserves_ready state.pending.size state scanned
          before top newRun prospectivePower result hmax hlayout hpowered hsplit
          hnewBase hnewNonnegative hnewPositive hnewWithin hprospectivePower
          hpowerRange
        · simpa [prospectivePower] using hfound
        · exact hcode
        · exact hfuel
      next hguard => simp at hfound

end CPythonListsort


-- created on 2026-10-23
-- updated on 2026-11-17
