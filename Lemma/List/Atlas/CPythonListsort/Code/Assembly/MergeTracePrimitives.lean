import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Assembly.MergeTracePrimitives
open CPythonListsort CPythonListsort.MergeMemcpySite CPythonListsort.TempRangeInBounds CPythonListsort.MergeMovementFrame CPythonListsort.MovementAccessOnly CPythonListsort.TempRangeInitialized CPythonListsort.TempRangeValuesMode CPythonListsort.AccessTrace CPythonListsort.AccessTrace.HasAccess CPythonListsort.AccessTrace.HasTempAccess CPythonListsort.MovementTraceSafe CPythonListsort.MovementTempLive
open SortSlice


namespace CPythonListsort.TempRangeInBounds

/--
[head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma head
  {storage : TempStorage κ ν}
  {start : Int}
  {count : Nat}
-- given
  (h : TempRangeInBounds storage start (count + 1)) :
-- imply
  TempIndexInBounds storage start := by
-- proof
  obtain ⟨hstart, hend⟩ := h
  constructor
  · exact hstart
  · simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hend ⊢
    omega

end CPythonListsort.TempRangeInBounds

namespace CPythonListsort.TempRangeInBounds

/--
[tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tail
  {storage : TempStorage κ ν}
  {start : Int}
  {count : Nat}
-- given
  (h : TempRangeInBounds storage start (count + 1)) :
-- imply
  TempRangeInBounds storage (start + 1) count := by
-- proof
  obtain ⟨hstart, hend⟩ := h
  constructor
  · omega
  · simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hend ⊢
    omega

end CPythonListsort.TempRangeInBounds

namespace CPythonListsort.TempRangeInBounds

/--
[of_size_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma of_size_eq
  {first second : TempStorage κ ν}
  {start : Int}
  {count : Nat}
-- given
  (h : TempRangeInBounds first start count)
  (hsize : second.cells.size = first.cells.size) :
-- imply
  TempRangeInBounds second start count := by
-- proof
  simpa [TempRangeInBounds, hsize] using h

end CPythonListsort.TempRangeInBounds

namespace CPythonListsort

/--
[erase_mergeTempRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma erase_mergeTempRead
  {storage : TempStorage κ ν}
  {index : Int} :
-- imply
  (TraceResult.tempPayloadRead? storage index).erase = mergeTempRead? storage index := by
-- proof
  simp [mergeTempRead?]

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeTempWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma erase_mergeTempWrite
  {storage : TempStorage κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν} :
-- imply
  (TraceResult.tempPayloadWrite? storage index entry).erase = mergeTempWrite? storage index entry := by
-- proof
  simp [mergeTempWrite?]

end CPythonListsort

namespace CPythonListsort

/--
[erase_mainToTempKeyTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma erase_mainToTempKeyTraced
  {state : MergeState κ ν}
  {tempDst mainSrc : Int} :
-- imply
  (mainToTempKeyTraced? state tempDst mainSrc).erase = mainToTempCell? state tempDst mainSrc := by
-- proof
  cases hread : state.data.read? mainSrc with
  | none => simp [mainToTempKeyTraced?, mainToTempCell?, hread]
  | some entry =>
    by_cases hbounds : 0 ≤ tempDst ∧ tempDst.toNat < state.a.cells.size <;>
      simp [mainToTempKeyTraced?, mainToTempCell?, mergeTempWrite?, hread,
        hbounds]

end CPythonListsort

namespace CPythonListsort

/--
[erase_mainToTempValuesTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma erase_mainToTempValuesTraced
  {state : MergeState κ ν}
  {tempDst mainSrc : Int} :
-- imply
  (mainToTempValuesTraced? state tempDst mainSrc).erase = mainToTempCell? state tempDst mainSrc := by
-- proof
  cases hread : state.data.read? mainSrc with
  | none => simp [mainToTempValuesTraced?, mainToTempCell?, hread]
  | some entry =>
    by_cases hbounds : 0 ≤ tempDst ∧ tempDst.toNat < state.a.cells.size <;>
      simp [mainToTempValuesTraced?, mainToTempCell?, mergeTempWrite?, hread,
        hbounds]

end CPythonListsort

namespace CPythonListsort

/--
[erase_mainToTempCellTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma erase_mainToTempCellTraced
  {state : MergeState κ ν}
  {tempDst mainSrc : Int} :
-- imply
  (mainToTempCellTraced? state tempDst mainSrc).erase = mainToTempCell? state tempDst mainSrc := by
-- proof
  unfold mainToTempCellTraced?
  rw [TraceResult.erase_bind, erase_mainToTempKeyTraced]
  cases hcopy : mainToTempCell? state tempDst mainSrc <;>
    cases hmode : state.a.hasValues <;>
    simp [hcopy]

end CPythonListsort

namespace CPythonListsort

/--
[erase_tempToMainKeyTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma erase_tempToMainKeyTraced
  {state : MergeState κ ν}
  {mainDst tempSrc : Int} :
-- imply
  (tempToMainKeyTraced? state mainDst tempSrc).erase = tempToMainCell? state mainDst tempSrc := by
-- proof
  unfold tempToMainKeyTraced? tempToMainCell?
  rw [TraceResult.erase_bind, erase_mergeTempRead]
  cases hread : mergeTempRead? state.a tempSrc with
  | none => simp
  | some entry =>
    cases hwrite : state.data.write? mainDst entry <;> simp [hwrite]

end CPythonListsort

namespace CPythonListsort

/--
[erase_tempToMainValuesTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma erase_tempToMainValuesTraced
  {state : MergeState κ ν}
  {mainDst tempSrc : Int} :
-- imply
  (tempToMainValuesTraced? state mainDst tempSrc).erase = tempToMainCell? state mainDst tempSrc := by
-- proof
  unfold tempToMainValuesTraced? tempToMainCell?
  rw [TraceResult.erase_bind, erase_mergeTempRead]
  cases hread : mergeTempRead? state.a tempSrc with
  | none => simp
  | some entry =>
    cases hwrite : state.data.write? mainDst entry <;> simp [hwrite]

end CPythonListsort

namespace CPythonListsort

/--
[erase_tempToMainCellTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma erase_tempToMainCellTraced
  {state : MergeState κ ν}
  {mainDst tempSrc : Int} :
-- imply
  (tempToMainCellTraced? state mainDst tempSrc).erase = tempToMainCell? state mainDst tempSrc := by
-- proof
  unfold tempToMainCellTraced?
  rw [TraceResult.erase_bind, erase_tempToMainKeyTraced]
  cases hcopy : tempToMainCell? state mainDst tempSrc <;>
    cases hmode : state.a.hasValues <;>
    simp [hcopy]

end CPythonListsort

namespace CPythonListsort

/--
[erase_mainToTempKeysTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma erase_mainToTempKeysTraced
  {site : MergeMemcpySite}
  {permit : site.MainToTempPermit}
  {count : Nat}
  {state : MergeState κ ν}
  {tempDst mainSrc : Int} :
-- imply
  (mainToTempKeysTraced? site permit count state tempDst mainSrc).erase = mainToTempMemcpy? count state tempDst mainSrc := by
-- proof
  induction count generalizing state tempDst mainSrc with
  | zero => rfl
  | succ count ih =>
    simp [mainToTempKeysTraced?, mainToTempMemcpy?, ih]

end CPythonListsort

namespace CPythonListsort

/--
[erase_mainToTempValuesPhaseTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma erase_mainToTempValuesPhaseTraced
  {site : MergeMemcpySite}
  {permit : site.MainToTempPermit}
  {count : Nat}
  {state : MergeState κ ν}
  {tempDst mainSrc : Int} :
-- imply
  (mainToTempValuesPhaseTraced? site permit count state tempDst mainSrc).erase = mainToTempMemcpy? count state tempDst mainSrc := by
-- proof
  induction count generalizing state tempDst mainSrc with
  | zero => rfl
  | succ count ih =>
    simp [mainToTempValuesPhaseTraced?, mainToTempMemcpy?, ih]

end CPythonListsort

namespace CPythonListsort

/--
[erase_mainToTempMemcpyTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma erase_mainToTempMemcpyTraced
  {site : MergeMemcpySite}
  {permit : site.MainToTempPermit}
  {count : Nat}
  {state : MergeState κ ν}
  {tempDst mainSrc : Int} :
-- imply
  (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).erase = mainToTempMemcpy? count state tempDst mainSrc := by
-- proof
  unfold mainToTempMemcpyTraced?
  rw [TraceResult.erase_bind, erase_mainToTempKeysTraced]
  cases hcopy : mainToTempMemcpy? count state tempDst mainSrc <;>
    cases hmode : state.a.hasValues <;>
    simp [hcopy]

end CPythonListsort

namespace CPythonListsort

/--
[erase_tempToMainKeysTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma erase_tempToMainKeysTraced
  {site : MergeMemcpySite}
  {permit : site.TempToMainPermit}
  {count : Nat}
  {state : MergeState κ ν}
  {mainDst tempSrc : Int} :
-- imply
  (tempToMainKeysTraced? site permit count state mainDst tempSrc).erase = tempToMainMemcpy? count state mainDst tempSrc := by
-- proof
  induction count generalizing state mainDst tempSrc with
  | zero => rfl
  | succ count ih =>
    simp [tempToMainKeysTraced?, tempToMainMemcpy?, ih]

end CPythonListsort

namespace CPythonListsort

/--
[erase_tempToMainValuesPhaseTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma erase_tempToMainValuesPhaseTraced
  {site : MergeMemcpySite}
  {permit : site.TempToMainPermit}
  {count : Nat}
  {state : MergeState κ ν}
  {mainDst tempSrc : Int} :
-- imply
  (tempToMainValuesPhaseTraced? site permit count state mainDst tempSrc).erase = tempToMainMemcpy? count state mainDst tempSrc := by
-- proof
  induction count generalizing state mainDst tempSrc with
  | zero => rfl
  | succ count ih =>
    simp [tempToMainValuesPhaseTraced?, tempToMainMemcpy?, ih]

end CPythonListsort

namespace CPythonListsort

/--
[erase_tempToMainMemcpyTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma erase_tempToMainMemcpyTraced
  {site : MergeMemcpySite}
  {permit : site.TempToMainPermit}
  {count : Nat}
  {state : MergeState κ ν}
  {mainDst tempSrc : Int} :
-- imply
  (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).erase = tempToMainMemcpy? count state mainDst tempSrc := by
-- proof
  unfold tempToMainMemcpyTraced?
  rw [TraceResult.erase_bind, erase_tempToMainKeysTraced]
  cases hcopy : tempToMainMemcpy? count state mainDst tempSrc <;>
    cases hmode : state.a.hasValues <;>
    simp [hcopy]

end CPythonListsort

namespace CPythonListsort

/--
[erase_mainDataMemmoveTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma erase_mainDataMemmoveTraced
  {state : MergeState κ ν}
  {dst src : Int}
  {count : Nat} :
-- imply
  (mainDataMemmoveTraced? state dst src count).erase = mainDataMemmove? state dst src count := by
-- proof
  cases hmove : state.data.memmove? dst src count <;>
    simp [mainDataMemmoveTraced?, mainDataMemmove?, hmove]

end CPythonListsort

namespace CPythonListsort.MergeMovementFrame

/--
[refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma refl
  {state : MergeState κ ν} :
-- imply
  MergeMovementFrame state state := by
-- proof
  constructor <;> rfl

end CPythonListsort.MergeMovementFrame

namespace CPythonListsort.MergeMovementFrame

/--
[trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma trans
  {first second third : MergeState κ ν}
-- given
  (h₁ : MergeMovementFrame first second)
  (h₂ : MergeMovementFrame second third) :
-- imply
  MergeMovementFrame first third := by
-- proof
  constructor
  · exact h₂.minGallop.trans h₁.minGallop
  · exact h₂.listlen.trans h₁.listlen
  · exact h₂.basekeys.trans h₁.basekeys
  · exact h₂.dataSize.trans h₁.dataSize
  · exact h₂.tempSize.trans h₁.tempSize
  · exact h₂.tempBacking.trans h₁.tempBacking
  · exact h₂.tempValuesMode.trans h₁.tempValuesMode
  · exact h₂.alloced.trans h₁.alloced
  · exact h₂.pending.trans h₁.pending
  · exact h₂.comparator.trans h₁.comparator
  · exact h₂.mrCurrent.trans h₁.mrCurrent
  · exact h₂.mrE.trans h₁.mrE
  · exact h₂.mrMask.trans h₁.mrMask

end CPythonListsort.MergeMovementFrame

namespace CPythonListsort.MergeMovementFrame

/--
[tempStorageInv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tempStorageInv
  {before after : MergeState κ ν}
-- given
  (hframe : MergeMovementFrame before after)
  (hinvariant : TempStorageInv before.a before.alloced) :
-- imply
  TempStorageInv after.a after.alloced := by
-- proof
  cases hbefore : before.a.backing with
  | inline =>
    have hafter : after.a.backing = .inline :=
      hframe.tempBacking.trans hbefore
    simp only [TempStorageInv, hbefore] at hinvariant
    simp only [TempStorageInv, hafter]
    simpa [TempStorage.multiplier, hframe.tempSize,
      hframe.tempValuesMode, hframe.alloced] using hinvariant
  | heap =>
    have hafter : after.a.backing = .heap :=
      hframe.tempBacking.trans hbefore
    simp only [TempStorageInv, hbefore] at hinvariant
    simp only [TempStorageInv, hafter]
    simpa [TempStorage.physicalSlots, TempStorage.multiplier,
      hframe.tempSize, hframe.tempValuesMode, hframe.alloced] using hinvariant
  | released =>
    have hafter : after.a.backing = .released :=
      hframe.tempBacking.trans hbefore
    simp only [TempStorageInv, hbefore, Array.isEmpty_iff] at hinvariant
    simp only [TempStorageInv, hafter, Array.isEmpty_iff]
    apply Array.size_eq_zero_iff.mp
    calc
      after.a.cells.size = before.a.cells.size := hframe.tempSize
      _ = 0 := by simpa using congrArg Array.size hinvariant

end CPythonListsort.MergeMovementFrame

namespace CPythonListsort.MergeMovementFrame

/--
[live](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma live
  {before after : MergeState κ ν}
-- given
  (hframe : MergeMovementFrame before after)
  (hlive : before.a.Live) :
-- imply
  after.a.Live := by
-- proof
  simpa [TempStorage.Live, hframe.tempBacking] using hlive

end CPythonListsort.MergeMovementFrame

namespace CPythonListsort

/--
[mainToTempCell_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma mainToTempCell_frame
  (state result : MergeState κ ν) (tempDst mainSrc : Int)
  (hresult : mainToTempCell? state tempDst mainSrc = some result) :
  MergeMovementFrame state result := by
  obtain ⟨entry, hread, htail⟩ := Option.bind_eq_some_iff.mp hresult
  obtain ⟨storage, hwrite, hfinal⟩ := Option.bind_eq_some_iff.mp htail
  change some { state with a := storage } = some result at hfinal
  injection hfinal with hfinal
  subst result
  have hsize : storage.cells.size = state.a.cells.size := by
    unfold mergeTempWrite? at hwrite
    split at hwrite <;> try contradiction
    injection hwrite with hwrite
    subst storage
    simp
  have hbacking : storage.backing = state.a.backing := by
    unfold mergeTempWrite? at hwrite
    split at hwrite <;> try contradiction
    injection hwrite with hwrite
    subst storage
    rfl
  have hvalues : storage.hasValues = state.a.hasValues := by
    unfold mergeTempWrite? at hwrite
    split at hwrite <;> try contradiction
    injection hwrite with hwrite
    subst storage
    rfl
  constructor <;> simp [hsize, hbacking, hvalues]

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainCell_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma tempToMainCell_frame
  (state result : MergeState κ ν) (mainDst tempSrc : Int)
  (hresult : tempToMainCell? state mainDst tempSrc = some result) :
  MergeMovementFrame state result := by
  obtain ⟨entry, hread, htail⟩ := Option.bind_eq_some_iff.mp hresult
  obtain ⟨data, hwrite, hfinal⟩ := Option.bind_eq_some_iff.mp htail
  change some { state with data := data } = some result at hfinal
  injection hfinal with hfinal
  subst result
  constructor <;> try rfl
  exact SortSlice.write_entries_size_of_eq_some _ _ _ _ hwrite

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempMemcpy_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainToTempMemcpy_frame
  {count : Nat}
  {state result : MergeState κ ν}
  {tempDst mainSrc : Int}
-- given
  (hresult : mainToTempMemcpy? count state tempDst mainSrc = some result) :
-- imply
  MergeMovementFrame state result := by
-- proof
  induction count generalizing state tempDst mainSrc with
  | zero =>
    simp only [mainToTempMemcpy?, Option.some.injEq] at hresult
    subst result
    exact .refl state
  | succ count ih =>
    simp only [mainToTempMemcpy?, bind, Option.bind] at hresult
    split at hresult <;> try contradiction
    rename_i next hcell
    exact (mainToTempCell_frame state next tempDst mainSrc hcell).trans
      (ih next (tempDst + 1) (mainSrc + 1) hresult)

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainMemcpy_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tempToMainMemcpy_frame
  {count : Nat}
  {state result : MergeState κ ν}
  {mainDst tempSrc : Int}
-- given
  (hresult : tempToMainMemcpy? count state mainDst tempSrc = some result) :
-- imply
  MergeMovementFrame state result := by
-- proof
  induction count generalizing state mainDst tempSrc with
  | zero =>
    simp only [tempToMainMemcpy?, Option.some.injEq] at hresult
    subst result
    exact .refl state
  | succ count ih =>
    simp only [tempToMainMemcpy?, bind, Option.bind] at hresult
    split at hresult <;> try contradiction
    rename_i next hcell
    exact (tempToMainCell_frame state next mainDst tempSrc hcell).trans
      (ih next (mainDst + 1) (tempSrc + 1) hresult)

end CPythonListsort

namespace CPythonListsort

/--
[mainDataMemmove_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainDataMemmove_frame
  {state result : MergeState κ ν}
  {dst src : Int}
  {count : Nat}
-- given
  (hresult : mainDataMemmove? state dst src count = some result) :
-- imply
  MergeMovementFrame state result := by
-- proof
  obtain ⟨data, hmove, hfinal⟩ := Option.bind_eq_some_iff.mp hresult
  change some { state with data := data } = some result at hfinal
  injection hfinal with hfinal
  subst result
  constructor <;> try rfl
  exact SortSlice.memmove_entries_size_of_eq_some _ _ _ _ _ hmove

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempMemcpyTraced_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainToTempMemcpyTraced_frame
  {site : MergeMemcpySite}
  {permit : site.MainToTempPermit}
  {count : Nat}
  {state result : MergeState κ ν}
  {tempDst mainSrc : Int}
-- given
  (hresult : (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).result = some result) :
-- imply
  MergeMovementFrame state result := by
-- proof
  apply mainToTempMemcpy_frame count state result tempDst mainSrc
  rwa [← erase_mainToTempMemcpyTraced site permit count state tempDst mainSrc]

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainMemcpyTraced_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tempToMainMemcpyTraced_frame
  {site : MergeMemcpySite}
  {permit : site.TempToMainPermit}
  {count : Nat}
  {state result : MergeState κ ν}
  {mainDst tempSrc : Int}
-- given
  (hresult : (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).result = some result) :
-- imply
  MergeMovementFrame state result := by
-- proof
  apply tempToMainMemcpy_frame count state result mainDst tempSrc
  rwa [← erase_tempToMainMemcpyTraced site permit count state mainDst tempSrc]

end CPythonListsort

namespace CPythonListsort

/--
[mainDataMemmoveTraced_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainDataMemmoveTraced_frame
  {state result : MergeState κ ν}
  {dst src : Int}
  {count : Nat}
-- given
  (hresult : (mainDataMemmoveTraced? state dst src count).result = some result) :
-- imply
  MergeMovementFrame state result := by
-- proof
  apply mainDataMemmove_frame state result dst src count
  rwa [← erase_mainDataMemmoveTraced state dst src count]

end CPythonListsort

namespace CPythonListsort.MovementAccessOnly

/--
[pure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma pure
  {value : α} :
-- imply
  MovementAccessOnly (TraceResult.pure value) := by
-- proof
  simp [MovementAccessOnly, TraceResult.pure, AccessTrace.empty]

end CPythonListsort.MovementAccessOnly

namespace CPythonListsort.MovementAccessOnly

/--
[map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma map
  {current : TraceResult α}
  {transform : α → β}
-- given
  (h : MovementAccessOnly current) :
-- imply
  MovementAccessOnly (current.map transform) :=
-- proof
h

end CPythonListsort.MovementAccessOnly

namespace CPythonListsort.MovementAccessOnly

/--
[bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma bind
  {current : TraceResult α}
  {next : α → TraceResult β}
-- given
  (hcurrent : MovementAccessOnly current)
  (hnext : ∀ value, MovementAccessOnly (next value)) :
-- imply
  MovementAccessOnly (current.bind next) := by
-- proof
  obtain ⟨hcurrentFuel, hcurrentPush⟩ := hcurrent
  cases hresult : current.result with
  | none =>
    simpa [MovementAccessOnly, TraceResult.trace_bind, hresult] using
      And.intro hcurrentFuel hcurrentPush
  | some value =>
    obtain ⟨hnextFuel, hnextPush⟩ := hnext value
    simp [MovementAccessOnly, TraceResult.trace_bind, hresult,
      AccessTrace.compose, hcurrentFuel, hcurrentPush, hnextFuel, hnextPush]

end CPythonListsort.MovementAccessOnly

namespace CPythonListsort

/--
[tempRead_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma tempRead_accessOnly (storage : TempStorage κ ν) (index : Int) :
  MovementAccessOnly (TraceResult.tempPayloadRead? storage index) := by
  simp [MovementAccessOnly, TraceResult.trace_tempPayloadRead,
    AccessTrace.singletonAccess]

end CPythonListsort

namespace CPythonListsort

/--
[tempWrite_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma tempWrite_accessOnly (storage : TempStorage κ ν) (index : Int)
  (entry : SortSliceEntry κ ν) :
  MovementAccessOnly (TraceResult.tempPayloadWrite? storage index entry) := by
  simp [MovementAccessOnly, TraceResult.trace_tempPayloadWrite,
    AccessTrace.singletonAccess]

end CPythonListsort

namespace CPythonListsort

/--
[keyRead_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma keyRead_accessOnly (slice : SortSlice κ ν) (index : Int) :
  MovementAccessOnly (TraceResult.sortSliceKeysRead? slice index) := by
  simp [MovementAccessOnly, TraceResult.trace_sortSliceKeysRead,
    AccessTrace.singletonAccess]

end CPythonListsort

namespace CPythonListsort

/--
[valuesRead_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma valuesRead_accessOnly (slice : SortSlice κ ν) (index : Int) :
  MovementAccessOnly (TraceResult.sortSliceValuesRead? slice index) := by
  simp [MovementAccessOnly, TraceResult.trace_sortSliceValuesRead,
    AccessTrace.singletonAccess]

end CPythonListsort

namespace CPythonListsort

/--
[keyWrite_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma keyWrite_accessOnly (slice : SortSlice κ ν) (index : Int)
  (entry : SortSliceEntry κ ν) :
  MovementAccessOnly (TraceResult.sortSliceKeysWrite? slice index entry) := by
  simp [MovementAccessOnly, TraceResult.trace_sortSliceKeysWrite,
    AccessTrace.singletonAccess]

end CPythonListsort

namespace CPythonListsort

/--
[valuesWrite_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma valuesWrite_accessOnly (slice : SortSlice κ ν) (index : Int)
  (entry : SortSliceEntry κ ν) :
  MovementAccessOnly (TraceResult.sortSliceValuesWrite? slice index entry) := by
  simp [MovementAccessOnly, TraceResult.trace_sortSliceValuesWrite,
    AccessTrace.singletonAccess]

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempCellTraced_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainToTempCellTraced_accessOnly
  {state : MergeState κ ν}
  {tempDst mainSrc : Int} :
-- imply
  MovementAccessOnly (mainToTempCellTraced? state tempDst mainSrc) := by
-- proof
  apply MovementAccessOnly.bind
  · apply MovementAccessOnly.bind
    · exact keyRead_accessOnly state.data mainSrc
    · intro entry
      exact MovementAccessOnly.map _ _ (tempWrite_accessOnly state.a tempDst entry)
  · intro keyResult
    cases hmode : state.a.hasValues with
    | false => simp [MovementAccessOnly.pure]
    | true =>
      simp only [↓reduceIte]
      apply MovementAccessOnly.bind
      · exact valuesRead_accessOnly state.data mainSrc
      · intro entry
        exact MovementAccessOnly.map _ _
          (tempWrite_accessOnly state.a tempDst entry)

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainCellTraced_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tempToMainCellTraced_accessOnly
  {state : MergeState κ ν}
  {mainDst tempSrc : Int} :
-- imply
  MovementAccessOnly (tempToMainCellTraced? state mainDst tempSrc) := by
-- proof
  apply MovementAccessOnly.bind
  · apply MovementAccessOnly.bind
    · exact tempRead_accessOnly state.a tempSrc
    · intro entry
      exact MovementAccessOnly.map _ _
        (keyWrite_accessOnly state.data mainDst entry)
  · intro keyResult
    cases hmode : state.a.hasValues with
    | false => simp [MovementAccessOnly.pure]
    | true =>
      simp only [↓reduceIte]
      apply MovementAccessOnly.bind
      · exact tempRead_accessOnly state.a tempSrc
      · intro entry
        exact MovementAccessOnly.map _ _
          (valuesWrite_accessOnly state.data mainDst entry)

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempKeysTraced_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma mainToTempKeysTraced_accessOnly (site : MergeMemcpySite)
  (permit : site.MainToTempPermit) (count : Nat)
  (state : MergeState κ ν) (tempDst mainSrc : Int) :
  MovementAccessOnly
    (mainToTempKeysTraced? site permit count state tempDst mainSrc) := by
  induction count generalizing state tempDst mainSrc with
  | zero => exact MovementAccessOnly.pure state
  | succ count ih =>
    apply MovementAccessOnly.bind
    · apply MovementAccessOnly.bind
      · exact keyRead_accessOnly state.data mainSrc
      · intro entry
        exact MovementAccessOnly.map _ _
          (tempWrite_accessOnly state.a tempDst entry)
    · intro next
      exact ih next (tempDst + 1) (mainSrc + 1)

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempValuesPhaseTraced_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma mainToTempValuesPhaseTraced_accessOnly (site : MergeMemcpySite)
  (permit : site.MainToTempPermit) (count : Nat)
  (state : MergeState κ ν) (tempDst mainSrc : Int) :
  MovementAccessOnly
    (mainToTempValuesPhaseTraced? site permit count state tempDst mainSrc) := by
  induction count generalizing state tempDst mainSrc with
  | zero => exact MovementAccessOnly.pure state
  | succ count ih =>
    apply MovementAccessOnly.bind
    · apply MovementAccessOnly.bind
      · exact valuesRead_accessOnly state.data mainSrc
      · intro entry
        exact MovementAccessOnly.map _ _
          (tempWrite_accessOnly state.a tempDst entry)
    · intro next
      exact ih next (tempDst + 1) (mainSrc + 1)

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempMemcpyTraced_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainToTempMemcpyTraced_accessOnly
  {site : MergeMemcpySite}
  {permit : site.MainToTempPermit}
  {count : Nat}
  {state : MergeState κ ν}
  {tempDst mainSrc : Int} :
-- imply
  MovementAccessOnly (mainToTempMemcpyTraced? site permit count state tempDst mainSrc) := by
-- proof
  apply MovementAccessOnly.bind
  · exact mainToTempKeysTraced_accessOnly site permit count state tempDst mainSrc
  · intro keyResult
    cases hmode : state.a.hasValues with
    | false => simp [MovementAccessOnly.pure]
    | true =>
      simpa [hmode] using
        mainToTempValuesPhaseTraced_accessOnly site permit count state
          tempDst mainSrc

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainKeysTraced_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma tempToMainKeysTraced_accessOnly (site : MergeMemcpySite)
  (permit : site.TempToMainPermit) (count : Nat)
  (state : MergeState κ ν) (mainDst tempSrc : Int) :
  MovementAccessOnly
    (tempToMainKeysTraced? site permit count state mainDst tempSrc) := by
  induction count generalizing state mainDst tempSrc with
  | zero => exact MovementAccessOnly.pure state
  | succ count ih =>
    apply MovementAccessOnly.bind
    · apply MovementAccessOnly.bind
      · exact tempRead_accessOnly state.a tempSrc
      · intro entry
        exact MovementAccessOnly.map _ _
          (keyWrite_accessOnly state.data mainDst entry)
    · intro next
      exact ih next (mainDst + 1) (tempSrc + 1)

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainValuesPhaseTraced_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma tempToMainValuesPhaseTraced_accessOnly (site : MergeMemcpySite)
  (permit : site.TempToMainPermit) (count : Nat)
  (state : MergeState κ ν) (mainDst tempSrc : Int) :
  MovementAccessOnly
    (tempToMainValuesPhaseTraced? site permit count state mainDst tempSrc) := by
  induction count generalizing state mainDst tempSrc with
  | zero => exact MovementAccessOnly.pure state
  | succ count ih =>
    apply MovementAccessOnly.bind
    · apply MovementAccessOnly.bind
      · exact tempRead_accessOnly state.a tempSrc
      · intro entry
        exact MovementAccessOnly.map _ _
          (valuesWrite_accessOnly state.data mainDst entry)
    · intro next
      exact ih next (mainDst + 1) (tempSrc + 1)

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainMemcpyTraced_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tempToMainMemcpyTraced_accessOnly
  {site : MergeMemcpySite}
  {permit : site.TempToMainPermit}
  {count : Nat}
  {state : MergeState κ ν}
  {mainDst tempSrc : Int} :
-- imply
  MovementAccessOnly (tempToMainMemcpyTraced? site permit count state mainDst tempSrc) := by
-- proof
  apply MovementAccessOnly.bind
  · exact tempToMainKeysTraced_accessOnly site permit count state mainDst tempSrc
  · intro keyResult
    cases hmode : state.a.hasValues with
    | false => simp [MovementAccessOnly.pure]
    | true =>
      simpa [hmode] using
        tempToMainValuesPhaseTraced_accessOnly site permit count state
          mainDst tempSrc

end CPythonListsort

namespace CPythonListsort

/--
[copyKeysFrom_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma copyKeysFrom_accessOnly (destination source : SortSlice κ ν)
  (dst src : Int) :
  MovementAccessOnly
    (SortSlice.copyKeysFromTraced? destination source dst src) := by
  apply MovementAccessOnly.bind
  · exact keyRead_accessOnly source src
  · intro entry
    exact keyWrite_accessOnly destination dst entry

end CPythonListsort

namespace CPythonListsort

/--
[copyValuesFrom_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma copyValuesFrom_accessOnly (destination source : SortSlice κ ν)
  (dst src : Int) :
  MovementAccessOnly
    (SortSlice.copyValuesFromTraced? destination source dst src) := by
  apply MovementAccessOnly.bind
  · exact valuesRead_accessOnly source src
  · intro entry
    exact valuesWrite_accessOnly destination dst entry

end CPythonListsort

namespace CPythonListsort

/--
[memmoveForwardKeys_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma memmoveForwardKeys_accessOnly (count : Nat)
  (slice : SortSlice κ ν) (dst src : Int) :
  MovementAccessOnly
    (SortSlice.memmoveForwardKeysTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact MovementAccessOnly.pure slice
  | succ count ih =>
    apply MovementAccessOnly.bind
    · exact copyKeysFrom_accessOnly slice slice dst src
    · intro updated
      exact ih updated (dst + 1) (src + 1)

end CPythonListsort

namespace CPythonListsort

/--
[memmoveForwardValues_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma memmoveForwardValues_accessOnly (count : Nat)
  (slice : SortSlice κ ν) (dst src : Int) :
  MovementAccessOnly
    (SortSlice.memmoveForwardValuesTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact MovementAccessOnly.pure slice
  | succ count ih =>
    apply MovementAccessOnly.bind
    · exact copyValuesFrom_accessOnly slice slice dst src
    · intro updated
      exact ih updated (dst + 1) (src + 1)

end CPythonListsort

namespace CPythonListsort

/--
[memmoveBackwardKeys_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma memmoveBackwardKeys_accessOnly (count : Nat)
  (slice : SortSlice κ ν) (dst src : Int) :
  MovementAccessOnly
    (SortSlice.memmoveBackwardKeysTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact MovementAccessOnly.pure slice
  | succ count ih =>
    apply MovementAccessOnly.bind
    · exact copyKeysFrom_accessOnly slice slice
      (dst + Int.ofNat count) (src + Int.ofNat count)
    · intro updated
      exact ih updated dst src

end CPythonListsort

namespace CPythonListsort

/--
[memmoveBackwardValues_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma memmoveBackwardValues_accessOnly (count : Nat)
  (slice : SortSlice κ ν) (dst src : Int) :
  MovementAccessOnly
    (SortSlice.memmoveBackwardValuesTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact MovementAccessOnly.pure slice
  | succ count ih =>
    apply MovementAccessOnly.bind
    · exact copyValuesFrom_accessOnly slice slice
      (dst + Int.ofNat count) (src + Int.ofNat count)
    · intro updated
      exact ih updated dst src

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceMemmove_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma sortSliceMemmove_accessOnly (valuesPresent : Bool)
  (slice : SortSlice κ ν) (dst src : Int) (count : Nat) :
  MovementAccessOnly
    (SortSlice.memmoveTraced? valuesPresent slice dst src count) := by
  cases hdirection : SortSlice.memmoveDirection dst src with
  | forward =>
    simp only [SortSlice.memmoveTraced?, hdirection]
    apply MovementAccessOnly.bind
    · exact memmoveForwardKeys_accessOnly count slice dst src
    · intro keyResult
      cases hvalues : valuesPresent with
      | false => simp [MovementAccessOnly.pure]
      | true =>
        simpa [hvalues] using
          memmoveForwardValues_accessOnly count slice dst src
  | backward =>
    simp only [SortSlice.memmoveTraced?, hdirection]
    apply MovementAccessOnly.bind
    · exact memmoveBackwardKeys_accessOnly count slice dst src
    · intro keyResult
      cases hvalues : valuesPresent with
      | false => simp [MovementAccessOnly.pure]
      | true =>
        simpa [hvalues] using
          memmoveBackwardValues_accessOnly count slice dst src

end CPythonListsort

namespace CPythonListsort

/--
[mainDataMemmoveTraced_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainDataMemmoveTraced_accessOnly
  {state : MergeState κ ν}
  {dst src : Int}
  {count : Nat} :
-- imply
  MovementAccessOnly (mainDataMemmoveTraced? state dst src count) := by
-- proof
  exact MovementAccessOnly.map _ _
    (sortSliceMemmove_accessOnly state.a.hasValues state.data dst src count)

end CPythonListsort

namespace CPythonListsort

/--
[mergeTempWrite_eq_some_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mergeTempWrite_eq_some_of_bounds
  {storage : TempStorage κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν}
-- given
  (hindex : TempIndexInBounds storage index) :
-- imply
  ∃ updated, mergeTempWrite? storage index entry = some updated := by
-- proof
  have hnat : index.toNat < storage.cells.size :=
    (Int.toNat_lt hindex.1).2 hindex.2
  refine ⟨{ storage with
    cells := storage.cells.setIfInBounds index.toNat (some entry) }, ?_⟩
  simp [mergeTempWrite?, hindex.1, hnat]

end CPythonListsort

namespace CPythonListsort

/--
[mergeTempWrite_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mergeTempWrite_size_of_eq_some
  {storage updated : TempStorage κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν}
-- given
  (hwrite : mergeTempWrite? storage index entry = some updated) :
-- imply
  updated.cells.size = storage.cells.size := by
-- proof
  unfold mergeTempWrite? at hwrite
  split at hwrite <;> try contradiction
  injection hwrite with hwrite
  subst updated
  simp

end CPythonListsort

namespace CPythonListsort

/--
[mergeTempWrite_backing_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mergeTempWrite_backing_of_eq_some
  {storage updated : TempStorage κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν}
-- given
  (hwrite : mergeTempWrite? storage index entry = some updated) :
-- imply
  updated.backing = storage.backing := by
-- proof
  unfold mergeTempWrite? at hwrite
  split at hwrite <;> try contradiction
  injection hwrite with hwrite
  subst updated
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeTempWrite_valuesMode_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mergeTempWrite_valuesMode_of_eq_some
  {storage updated : TempStorage κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν}
-- given
  (hwrite : mergeTempWrite? storage index entry = some updated) :
-- imply
  updated.hasValues = storage.hasValues := by
-- proof
  unfold mergeTempWrite? at hwrite
  split at hwrite <;> try contradiction
  injection hwrite with hwrite
  subst updated
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeTempWrite_read_self_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mergeTempWrite_read_self_of_eq_some
  {storage updated : TempStorage κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν}
-- given
  (hwrite : mergeTempWrite? storage index entry = some updated) :
-- imply
  mergeTempRead? updated index = some entry := by
-- proof
  unfold mergeTempWrite? at hwrite
  split at hwrite
  · rename_i hbounds
    injection hwrite with hwrite
    subst updated
    have hnonnegative := hbounds.1
    have hnat := hbounds.2
    simp [mergeTempRead?, hnonnegative, hnat]
  · contradiction

end CPythonListsort

namespace CPythonListsort

/--
[mergeTempWrite_read_ne_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mergeTempWrite_read_ne_of_eq_some
  {storage updated : TempStorage κ ν}
  {written other : Int}
  {entry : SortSliceEntry κ ν}
-- given
  (hwrite : mergeTempWrite? storage written entry = some updated)
  (hne : other ≠ written) :
-- imply
  mergeTempRead? updated other = mergeTempRead? storage other := by
-- proof
  unfold mergeTempWrite? at hwrite
  split at hwrite
  · rename_i hbounds
    injection hwrite with hwrite
    subst updated
    by_cases hother : 0 ≤ other
    · have hnatne : written.toNat ≠ other.toNat := by
      intro heq
      apply hne
      have hwrittenCast := Int.toNat_of_nonneg hbounds.1
      have hotherCast := Int.toNat_of_nonneg hother
      omega
      simp [mergeTempRead?, hother, hnatne]
    · simp [mergeTempRead?, hother]
  · contradiction

end CPythonListsort

namespace CPythonListsort.TempRangeInitialized

/--
[head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma head
  {storage : TempStorage κ ν}
  {start : Int}
  {count : Nat}
-- given
  (h : TempRangeInitialized storage start (count + 1)) :
-- imply
  ∃ entry, mergeTempRead? storage start = some entry := by
-- proof
  obtain ⟨entry, hentry⟩ := h 0 (Nat.zero_lt_succ count)
  rw [erase_mergeTempRead] at hentry
  have hzero : start + Int.ofNat 0 = start := by
    simp [Int.ofNat_eq_natCast]
  rw [hzero] at hentry
  exact ⟨entry, hentry⟩

end CPythonListsort.TempRangeInitialized

namespace CPythonListsort.TempRangeInitialized

/--
[tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tail
  {storage : TempStorage κ ν}
  {start : Int}
  {count : Nat}
-- given
  (h : TempRangeInitialized storage start (count + 1)) :
-- imply
  TempRangeInitialized storage (start + 1) count := by
-- proof
  intro offset hoffset
  obtain ⟨entry, hentry⟩ := h (offset + 1) (by omega)
  refine ⟨entry, ?_⟩
  have hindex : start + Int.ofNat (offset + 1) =
    start + 1 + Int.ofNat offset := by
    simp [Int.ofNat_eq_natCast, add_left_comm, add_comm]
  simpa only [hindex] using hentry

end CPythonListsort.TempRangeInitialized

namespace CPythonListsort.TempRangeValuesMode

/--
[head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma head
  {storage : TempStorage κ ν}
  {start : Int}
  {count : Nat}
-- given
  (h : TempRangeValuesMode storage start (count + 1)) :
-- imply
  ∃ entry, mergeTempRead? storage start = some entry ∧ SortSlice.EntryMatchesValuesMode storage.hasValues entry := by
-- proof
  obtain ⟨entry, hread, hmode⟩ := h 0 (Nat.zero_lt_succ count)
  rw [erase_mergeTempRead] at hread
  have hzero : start + Int.ofNat 0 = start := by
    simp [Int.ofNat_eq_natCast]
  rw [hzero] at hread
  exact ⟨entry, hread, hmode⟩

end CPythonListsort.TempRangeValuesMode

namespace CPythonListsort.TempRangeValuesMode

/--
[tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tail
  {storage : TempStorage κ ν}
  {start : Int}
  {count : Nat}
-- given
  (h : TempRangeValuesMode storage start (count + 1)) :
-- imply
  TempRangeValuesMode storage (start + 1) count := by
-- proof
  intro offset hoffset
  obtain ⟨entry, hread, hmode⟩ := h (offset + 1) (by omega)
  refine ⟨entry, ?_, hmode⟩
  have hindex : start + Int.ofNat (offset + 1) =
    start + 1 + Int.ofNat offset := by
    simp [Int.ofNat_eq_natCast, add_left_comm, add_comm]
  simpa only [hindex] using hread

end CPythonListsort.TempRangeValuesMode

namespace CPythonListsort.AccessTrace.HasAccess

/--
[compose_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma compose_left
  {earlier later : AccessTrace}
  {kind : AccessKind}
  {region : AccessRegion}
-- given
  (h : earlier.HasAccess kind region) :
-- imply
  (earlier.compose later).HasAccess kind region := by
-- proof
  obtain ⟨event, hevent, hkind, hregion⟩ := h
  exact ⟨event, by simp [AccessTrace.compose, hevent], hkind, hregion⟩

end CPythonListsort.AccessTrace.HasAccess

namespace CPythonListsort.AccessTrace.HasAccess

/--
[compose_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma compose_right
  {earlier later : AccessTrace}
  {kind : AccessKind}
  {region : AccessRegion}
-- given
  (h : later.HasAccess kind region) :
-- imply
  (earlier.compose later).HasAccess kind region := by
-- proof
  obtain ⟨event, hevent, hkind, hregion⟩ := h
  exact ⟨event, by simp [AccessTrace.compose, hevent], hkind, hregion⟩

end CPythonListsort.AccessTrace.HasAccess

namespace CPythonListsort.AccessTrace.HasAccess

/--
[accesses_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma accesses_ne_nil
  {trace : AccessTrace}
  {kind : AccessKind}
  {region : AccessRegion}
-- given
  (h : trace.HasAccess kind region) :
-- imply
  trace.accesses ≠ [] := by
-- proof
  intro hempty
  obtain ⟨event, hevent, _, _⟩ := h
  simp [hempty] at hevent

end CPythonListsort.AccessTrace.HasAccess

namespace CPythonListsort.AccessTrace.HasTempAccess

/--
[compose_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma compose_left
  {earlier later : AccessTrace}
  {kind : AccessKind}
-- given
  (h : earlier.HasTempAccess kind) :
-- imply
  (earlier.compose later).HasTempAccess kind := by
-- proof
  obtain ⟨backing, haccess⟩ := h
  exact ⟨backing, haccess.compose_left⟩

end CPythonListsort.AccessTrace.HasTempAccess

namespace CPythonListsort.AccessTrace.HasTempAccess

/--
[compose_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma compose_right
  {earlier later : AccessTrace}
  {kind : AccessKind}
-- given
  (h : later.HasTempAccess kind) :
-- imply
  (earlier.compose later).HasTempAccess kind := by
-- proof
  obtain ⟨backing, haccess⟩ := h
  exact ⟨backing, haccess.compose_right⟩

end CPythonListsort.AccessTrace.HasTempAccess

namespace CPythonListsort.MovementTraceSafe

/--
[pure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma pure
  {value : α} :
-- imply
  MovementTraceSafe (TraceResult.pure value) := by
-- proof
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact AccessTrace.allAccessesInBounds_empty
  · exact AccessTrace.tempPayloadAccessesLive_empty

end CPythonListsort.MovementTraceSafe

namespace CPythonListsort.MovementTraceSafe

/--
[map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma map
  {current : TraceResult α}
  {transform : α → β}
-- given
  (h : MovementTraceSafe current) :
-- imply
  MovementTraceSafe (current.map transform) :=
-- proof
⟨h.fuel, h.noPushes, h.bounds, h.tempLive⟩

end CPythonListsort.MovementTraceSafe

namespace CPythonListsort.MovementTraceSafe

/--
[recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent}
-- given
  (h : MovementTraceSafe current) :
-- imply
  MovementTraceSafe (current.recordSuccessMemoryEvent event) := by
-- proof
  exact
    { fuel := by simpa using h.fuel
      noPushes := by simpa using h.noPushes
      bounds := (TraceResult.allAccessesInBounds_recordSuccessMemoryEvent
        current event).2 h.bounds
      tempLive :=
        (TraceResult.tempPayloadAccessesLive_recordSuccessMemoryEvent
          current event).2 h.tempLive }

end CPythonListsort.MovementTraceSafe

namespace CPythonListsort

/--
[keyRead_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma keyRead_safe (slice : SortSlice κ ν) (index : Int)
  (hindex : SortSlice.IndexInBounds slice index) :
  MovementTraceSafe (TraceResult.sortSliceKeysRead? slice index) := by
  constructor
  · simp [TraceResult.trace_sortSliceKeysRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceKeysRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_sortSliceKeysRead]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, SortSlice.IndexInBounds] using hindex
  · simp [TraceResult.trace_sortSliceKeysRead,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort

namespace CPythonListsort

/--
[valuesRead_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma valuesRead_safe (slice : SortSlice κ ν) (index : Int)
  (hindex : SortSlice.IndexInBounds slice index) :
  MovementTraceSafe (TraceResult.sortSliceValuesRead? slice index) := by
  constructor
  · simp [TraceResult.trace_sortSliceValuesRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceValuesRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_sortSliceValuesRead]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, SortSlice.IndexInBounds] using hindex
  · simp [TraceResult.trace_sortSliceValuesRead,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort

namespace CPythonListsort

/--
[keyWrite_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma keyWrite_safe (slice : SortSlice κ ν) (index : Int)
  (entry : SortSliceEntry κ ν) (hindex : SortSlice.IndexInBounds slice index) :
  MovementTraceSafe (TraceResult.sortSliceKeysWrite? slice index entry) := by
  constructor
  · simp [TraceResult.trace_sortSliceKeysWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceKeysWrite, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_sortSliceKeysWrite]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, SortSlice.IndexInBounds] using hindex
  · simp [TraceResult.trace_sortSliceKeysWrite,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort

namespace CPythonListsort

/--
[valuesWrite_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma valuesWrite_safe (slice : SortSlice κ ν) (index : Int)
  (entry : SortSliceEntry κ ν) (hindex : SortSlice.IndexInBounds slice index) :
  MovementTraceSafe (TraceResult.sortSliceValuesWrite? slice index entry) := by
  constructor
  · simp [TraceResult.trace_sortSliceValuesWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceValuesWrite, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_sortSliceValuesWrite]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, SortSlice.IndexInBounds] using hindex
  · simp [TraceResult.trace_sortSliceValuesWrite,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort

namespace CPythonListsort

/--
[tempRead_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma tempRead_safe (storage : TempStorage κ ν) (index : Int)
  (hindex : TempIndexInBounds storage index) (hlive : storage.Live) :
  MovementTraceSafe (TraceResult.tempPayloadRead? storage index) := by
  constructor
  · simp [TraceResult.trace_tempPayloadRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_tempPayloadRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_tempPayloadRead]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, TempIndexInBounds] using hindex
  · rw [TraceResult.trace_tempPayloadRead]
    simpa [AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive, TempStorage.Live] using hlive

end CPythonListsort

namespace CPythonListsort

/--
[tempWrite_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma tempWrite_safe (storage : TempStorage κ ν) (index : Int)
  (entry : SortSliceEntry κ ν) (hindex : TempIndexInBounds storage index)
  (hlive : storage.Live) :
  MovementTraceSafe (TraceResult.tempPayloadWrite? storage index entry) := by
  constructor
  · simp [TraceResult.trace_tempPayloadWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_tempPayloadWrite, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_tempPayloadWrite]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, TempIndexInBounds] using hindex
  · rw [TraceResult.trace_tempPayloadWrite]
    simpa [AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive, TempStorage.Live] using hlive

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempCell_eq_some_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainToTempCell_eq_some_of_bounds
  {state : MergeState κ ν}
  {tempDst mainSrc : Int}
-- given
  (htemp : TempIndexInBounds state.a tempDst)
  (hmain : SortSlice.IndexInBounds state.data mainSrc) :
-- imply
  ∃ result, mainToTempCell? state tempDst mainSrc = some result := by
-- proof
  rcases SortSlice.read_eq_some_of_indexInBounds state.data mainSrc hmain with
    ⟨entry, hread⟩
  rcases mergeTempWrite_eq_some_of_bounds state.a tempDst entry htemp with
    ⟨storage, hwrite⟩
  refine ⟨{ state with a := storage }, ?_⟩
  simp [mainToTempCell?, hread, hwrite]

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainCell_eq_some_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tempToMainCell_eq_some_of_bounds
  {state : MergeState κ ν}
  {mainDst tempSrc : Int}
-- given
  (hmain : SortSlice.IndexInBounds state.data mainDst)
  (hreadable : ∃ entry, mergeTempRead? state.a tempSrc = some entry) :
-- imply
  ∃ result, tempToMainCell? state mainDst tempSrc = some result := by
-- proof
  obtain ⟨entry, hread⟩ := hreadable
  rcases SortSlice.write_eq_some_of_indexInBounds state.data mainDst entry hmain with
    ⟨data, hwrite⟩
  refine ⟨{ state with data := data }, ?_⟩
  simp [tempToMainCell?, hread, hwrite]

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempCell_data_eq_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainToTempCell_data_eq_of_eq_some
  {state result : MergeState κ ν}
  {tempDst mainSrc : Int}
-- given
  (hresult : mainToTempCell? state tempDst mainSrc = some result) :
-- imply
  result.data = state.data := by
-- proof
  obtain ⟨entry, hread, htail⟩ := Option.bind_eq_some_iff.mp hresult
  obtain ⟨storage, hwrite, hfinal⟩ := Option.bind_eq_some_iff.mp htail
  change some { state with a := storage } = some result at hfinal
  injection hfinal with hfinal
  subst result
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainCell_temp_eq_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tempToMainCell_temp_eq_of_eq_some
  {state result : MergeState κ ν}
  {mainDst tempSrc : Int}
-- given
  (hresult : tempToMainCell? state mainDst tempSrc = some result) :
-- imply
  result.a = state.a := by
-- proof
  obtain ⟨entry, hread, htail⟩ := Option.bind_eq_some_iff.mp hresult
  obtain ⟨data, hwrite, hfinal⟩ := Option.bind_eq_some_iff.mp htail
  change some { state with data := data } = some result at hfinal
  injection hfinal with hfinal
  subst result
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempKeyTraced_safe_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma mainToTempKeyTraced_safe_of_bounds
  (state : MergeState κ ν) (tempDst mainSrc : Int)
  (htemp : TempIndexInBounds state.a tempDst)
  (hmain : SortSlice.IndexInBounds state.data mainSrc)
  (hlive : state.a.Live) :
  MovementTraceSafe (mainToTempKeyTraced? state tempDst mainSrc) := by
  rcases SortSlice.read_eq_some_of_indexInBounds state.data mainSrc hmain with
    ⟨entry, hread⟩
  have hreadTraced :
    (TraceResult.sortSliceKeysRead? state.data mainSrc).result = some entry := by
    change (TraceResult.sortSliceKeysRead? state.data mainSrc).erase = some entry
    simpa using hread
  unfold mainToTempKeyTraced?
  apply MovementTraceSafe.bind _ _ entry hreadTraced
  · exact keyRead_safe state.data mainSrc hmain
  · exact MovementTraceSafe.map _ _
    (tempWrite_safe state.a tempDst entry htemp hlive)

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempValuesTraced_safe_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma mainToTempValuesTraced_safe_of_bounds
  (state : MergeState κ ν) (tempDst mainSrc : Int)
  (htemp : TempIndexInBounds state.a tempDst)
  (hmain : SortSlice.IndexInBounds state.data mainSrc)
  (hlive : state.a.Live) :
  MovementTraceSafe (mainToTempValuesTraced? state tempDst mainSrc) := by
  rcases SortSlice.read_eq_some_of_indexInBounds state.data mainSrc hmain with
    ⟨entry, hread⟩
  have hreadTraced :
    (TraceResult.sortSliceValuesRead? state.data mainSrc).result = some entry := by
    change (TraceResult.sortSliceValuesRead? state.data mainSrc).erase = some entry
    simpa using hread
  unfold mainToTempValuesTraced?
  apply MovementTraceSafe.bind _ _ entry hreadTraced
  · exact valuesRead_safe state.data mainSrc hmain
  · exact MovementTraceSafe.map _ _
    (tempWrite_safe state.a tempDst entry htemp hlive)

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempCellTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainToTempCellTraced_safe
  {state : MergeState κ ν}
  {tempDst mainSrc : Int}
-- given
  (htemp : TempIndexInBounds state.a tempDst)
  (hmain : SortSlice.IndexInBounds state.data mainSrc)
  (hlive : state.a.Live) :
-- imply
  ∃ result, (mainToTempCellTraced? state tempDst mainSrc).result = some result ∧ MovementTraceSafe (mainToTempCellTraced? state tempDst mainSrc) ∧ MergeMovementFrame state result := by
-- proof
  rcases mainToTempCell_eq_some_of_bounds state tempDst mainSrc htemp hmain with
    ⟨result, hcore⟩
  have hkey : (mainToTempKeyTraced? state tempDst mainSrc).result = some result := by
    change (mainToTempKeyTraced? state tempDst mainSrc).erase = some result
    rwa [erase_mainToTempKeyTraced]
  have hexecution :
    (mainToTempCellTraced? state tempDst mainSrc).result = some result := by
    change (mainToTempCellTraced? state tempDst mainSrc).erase = some result
    rwa [erase_mainToTempCellTraced]
  refine ⟨result, hexecution, ?_, mainToTempCell_frame state result tempDst mainSrc hcore⟩
  unfold mainToTempCellTraced?
  apply MovementTraceSafe.bind _ _ result hkey
  · exact mainToTempKeyTraced_safe_of_bounds state tempDst mainSrc htemp hmain hlive
  · cases hmode : state.a.hasValues with
    | false => simp only [Bool.false_eq]
      exact MovementTraceSafe.pure result
    | true => simp only [↓reduceIte]
      exact mainToTempValuesTraced_safe_of_bounds state tempDst mainSrc
        htemp hmain hlive

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainKeyTraced_safe_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma tempToMainKeyTraced_safe_of_bounds
  (state : MergeState κ ν) (mainDst tempSrc : Int)
  (hmain : SortSlice.IndexInBounds state.data mainDst)
  (htemp : TempIndexInBounds state.a tempSrc)
  (hlive : state.a.Live)
  (hreadable : ∃ entry, mergeTempRead? state.a tempSrc = some entry) :
  MovementTraceSafe (tempToMainKeyTraced? state mainDst tempSrc) := by
  obtain ⟨entry, hread⟩ := hreadable
  have hreadTraced :
    (TraceResult.tempPayloadRead? state.a tempSrc).result = some entry := by
    change (TraceResult.tempPayloadRead? state.a tempSrc).erase = some entry
    rwa [erase_mergeTempRead]
  unfold tempToMainKeyTraced?
  apply MovementTraceSafe.bind _ _ entry hreadTraced
  · exact tempRead_safe state.a tempSrc htemp hlive
  · exact MovementTraceSafe.map _ _
    (keyWrite_safe state.data mainDst entry hmain)

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainValuesTraced_safe_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma tempToMainValuesTraced_safe_of_bounds
  (state : MergeState κ ν) (mainDst tempSrc : Int)
  (hmain : SortSlice.IndexInBounds state.data mainDst)
  (htemp : TempIndexInBounds state.a tempSrc)
  (hlive : state.a.Live)
  (hreadable : ∃ entry, mergeTempRead? state.a tempSrc = some entry) :
  MovementTraceSafe (tempToMainValuesTraced? state mainDst tempSrc) := by
  obtain ⟨entry, hread⟩ := hreadable
  have hreadTraced :
    (TraceResult.tempPayloadRead? state.a tempSrc).result = some entry := by
    change (TraceResult.tempPayloadRead? state.a tempSrc).erase = some entry
    rwa [erase_mergeTempRead]
  unfold tempToMainValuesTraced?
  apply MovementTraceSafe.bind _ _ entry hreadTraced
  · exact tempRead_safe state.a tempSrc htemp hlive
  · exact MovementTraceSafe.map _ _
    (valuesWrite_safe state.data mainDst entry hmain)

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainCellTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tempToMainCellTraced_safe
  {state : MergeState κ ν}
  {mainDst tempSrc : Int}
-- given
  (hmain : SortSlice.IndexInBounds state.data mainDst)
  (htemp : TempIndexInBounds state.a tempSrc)
  (hlive : state.a.Live)
  (hreadable : ∃ entry, mergeTempRead? state.a tempSrc = some entry) :
-- imply
  ∃ result, (tempToMainCellTraced? state mainDst tempSrc).result = some result ∧ MovementTraceSafe (tempToMainCellTraced? state mainDst tempSrc) ∧ MergeMovementFrame state result := by
-- proof
  rcases tempToMainCell_eq_some_of_bounds state mainDst tempSrc hmain hreadable with
    ⟨result, hcore⟩
  have hkey : (tempToMainKeyTraced? state mainDst tempSrc).result = some result := by
    change (tempToMainKeyTraced? state mainDst tempSrc).erase = some result
    rwa [erase_tempToMainKeyTraced]
  have hexecution :
    (tempToMainCellTraced? state mainDst tempSrc).result = some result := by
    change (tempToMainCellTraced? state mainDst tempSrc).erase = some result
    rwa [erase_tempToMainCellTraced]
  refine ⟨result, hexecution, ?_, tempToMainCell_frame state result mainDst tempSrc hcore⟩
  unfold tempToMainCellTraced?
  apply MovementTraceSafe.bind _ _ result hkey
  · exact tempToMainKeyTraced_safe_of_bounds state mainDst tempSrc hmain htemp
    hlive hreadable
  · cases hmode : state.a.hasValues with
    | false => simp only [Bool.false_eq]
      exact MovementTraceSafe.pure result
    | true => simp only [↓reduceIte]
      exact tempToMainValuesTraced_safe_of_bounds state mainDst tempSrc
        hmain htemp hlive hreadable

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempKeysTraced_safe_of_ranges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma mainToTempKeysTraced_safe_of_ranges (site : MergeMemcpySite)
  (permit : site.MainToTempPermit) (count : Nat)
  (state : MergeState κ ν) (tempDst mainSrc : Int)
  (htemp : TempRangeInBounds state.a tempDst count)
  (hmain : SortSlice.RangeInBounds state.data mainSrc count)
  (hlive : state.a.Live) :
  ∃ result,
    (mainToTempKeysTraced? site permit count state tempDst mainSrc).result =
      some result ∧
    MovementTraceSafe
      (mainToTempKeysTraced? site permit count state tempDst mainSrc) ∧
    MergeMovementFrame state result := by
  induction count generalizing state tempDst mainSrc with
  | zero =>
    refine ⟨state, rfl, MovementTraceSafe.pure state, .refl state⟩
  | succ count ih =>
    have htempHead := htemp.head
    have hmainHead := hmain.head
    rcases mainToTempCell_eq_some_of_bounds state tempDst mainSrc htempHead
      hmainHead with ⟨next, hcell⟩
    have hcellFrame := mainToTempCell_frame state next tempDst mainSrc hcell
    have hcellResult :
      (mainToTempKeyTraced? state tempDst mainSrc).result = some next := by
      change (mainToTempKeyTraced? state tempDst mainSrc).erase = some next
      rwa [erase_mainToTempKeyTraced]
    have htempTail : TempRangeInBounds next.a (tempDst + 1) count :=
      TempRangeInBounds.of_size_eq htemp.tail hcellFrame.tempSize
    have hmainTail : SortSlice.RangeInBounds next.data (mainSrc + 1) count :=
      SortSlice.RangeInBounds.of_size_eq hmain.tail hcellFrame.dataSize
    have hliveNext : next.a.Live := hcellFrame.live hlive
    rcases ih next (tempDst + 1) (mainSrc + 1) htempTail hmainTail hliveNext with
      ⟨result, hrest, hrestSafe, hrestFrame⟩
    refine ⟨result, ?_, ?_, hcellFrame.trans hrestFrame⟩
    · simp [mainToTempKeysTraced?, TraceResult.bind, hcellResult, hrest]
    · simp only [mainToTempKeysTraced?]
      exact MovementTraceSafe.bind _ _ next hcellResult
        (mainToTempKeyTraced_safe_of_bounds state tempDst mainSrc htempHead
          hmainHead hlive) hrestSafe

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempValuesPhaseTraced_safe_of_ranges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma mainToTempValuesPhaseTraced_safe_of_ranges
  (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
  (state : MergeState κ ν) (tempDst mainSrc : Int)
  (htemp : TempRangeInBounds state.a tempDst count)
  (hmain : SortSlice.RangeInBounds state.data mainSrc count)
  (hlive : state.a.Live) :
  ∃ result,
    (mainToTempValuesPhaseTraced? site permit count state tempDst mainSrc).result =
      some result ∧
    MovementTraceSafe
      (mainToTempValuesPhaseTraced? site permit count state tempDst mainSrc) ∧
    MergeMovementFrame state result := by
  induction count generalizing state tempDst mainSrc with
  | zero =>
    refine ⟨state, rfl, MovementTraceSafe.pure state, .refl state⟩
  | succ count ih =>
    have htempHead := htemp.head
    have hmainHead := hmain.head
    rcases mainToTempCell_eq_some_of_bounds state tempDst mainSrc htempHead
      hmainHead with ⟨next, hcell⟩
    have hcellFrame := mainToTempCell_frame state next tempDst mainSrc hcell
    have hcellResult :
      (mainToTempValuesTraced? state tempDst mainSrc).result = some next := by
      change (mainToTempValuesTraced? state tempDst mainSrc).erase = some next
      rwa [erase_mainToTempValuesTraced]
    have htempTail : TempRangeInBounds next.a (tempDst + 1) count :=
      TempRangeInBounds.of_size_eq htemp.tail hcellFrame.tempSize
    have hmainTail : SortSlice.RangeInBounds next.data (mainSrc + 1) count :=
      SortSlice.RangeInBounds.of_size_eq hmain.tail hcellFrame.dataSize
    have hliveNext : next.a.Live := hcellFrame.live hlive
    rcases ih next (tempDst + 1) (mainSrc + 1) htempTail hmainTail hliveNext with
      ⟨result, hrest, hrestSafe, hrestFrame⟩
    refine ⟨result, ?_, ?_, hcellFrame.trans hrestFrame⟩
    · simp [mainToTempValuesPhaseTraced?, TraceResult.bind, hcellResult, hrest]
    · simp only [mainToTempValuesPhaseTraced?]
      exact MovementTraceSafe.bind _ _ next hcellResult
        (mainToTempValuesTraced_safe_of_bounds state tempDst mainSrc htempHead
          hmainHead hlive) hrestSafe

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempMemcpyTraced_traceSafe_of_ranges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma mainToTempMemcpyTraced_traceSafe_of_ranges
  (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
  (state : MergeState κ ν) (tempDst mainSrc : Int)
  (htemp : TempRangeInBounds state.a tempDst count)
  (hmain : SortSlice.RangeInBounds state.data mainSrc count)
  (hlive : state.a.Live) :
  ∃ result,
    (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).result =
      some result ∧
    MovementTraceSafe
      (mainToTempMemcpyTraced? site permit count state tempDst mainSrc) ∧
    MergeMovementFrame state result := by
  rcases mainToTempKeysTraced_safe_of_ranges site permit count state tempDst
    mainSrc htemp hmain hlive with ⟨keyResult, hkeys, hkeysSafe, hkeysFrame⟩
  cases hmode : state.a.hasValues with
  | false =>
    refine ⟨keyResult, ?_, ?_, hkeysFrame⟩
    · simp [mainToTempMemcpyTraced?, TraceResult.bind, TraceResult.pure,
      hkeys, hmode]
    · unfold mainToTempMemcpyTraced?
      apply MovementTraceSafe.bind _ _ keyResult hkeys hkeysSafe
      simp only [hmode, Bool.false_eq]
      exact MovementTraceSafe.pure keyResult
  | true =>
    rcases mainToTempValuesPhaseTraced_safe_of_ranges site permit count state
      tempDst mainSrc htemp hmain hlive with
      ⟨valuesResult, hvalues, hvaluesSafe, hvaluesFrame⟩
    refine ⟨valuesResult, ?_, ?_, hvaluesFrame⟩
    · simp [mainToTempMemcpyTraced?, TraceResult.bind, hkeys, hmode, hvalues]
    · unfold mainToTempMemcpyTraced?
      apply MovementTraceSafe.bind _ _ keyResult hkeys hkeysSafe
      simpa only [hmode, Bool.true_eq, ↓reduceIte] using hvaluesSafe

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainKeysTraced_safe_of_ranges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma tempToMainKeysTraced_safe_of_ranges (site : MergeMemcpySite)
  (permit : site.TempToMainPermit) (count : Nat)
  (state : MergeState κ ν) (mainDst tempSrc : Int)
  (hmain : SortSlice.RangeInBounds state.data mainDst count)
  (htemp : TempRangeInBounds state.a tempSrc count)
  (hinitialized : TempRangeInitialized state.a tempSrc count)
  (hlive : state.a.Live) :
  ∃ result,
    (tempToMainKeysTraced? site permit count state mainDst tempSrc).result =
      some result ∧
    MovementTraceSafe
      (tempToMainKeysTraced? site permit count state mainDst tempSrc) ∧
    MergeMovementFrame state result := by
  induction count generalizing state mainDst tempSrc with
  | zero =>
    refine ⟨state, rfl, MovementTraceSafe.pure state, .refl state⟩
  | succ count ih =>
    have hmainHead := hmain.head
    have htempHead := htemp.head
    have hreadable := hinitialized.head
    rcases tempToMainCell_eq_some_of_bounds state mainDst tempSrc hmainHead
      hreadable with ⟨next, hcell⟩
    have hcellFrame := tempToMainCell_frame state next mainDst tempSrc hcell
    have htempEq := tempToMainCell_temp_eq_of_eq_some state next mainDst tempSrc hcell
    have hcellResult :
      (tempToMainKeyTraced? state mainDst tempSrc).result = some next := by
      change (tempToMainKeyTraced? state mainDst tempSrc).erase = some next
      rwa [erase_tempToMainKeyTraced]
    have hmainTail : SortSlice.RangeInBounds next.data (mainDst + 1) count :=
      SortSlice.RangeInBounds.of_size_eq hmain.tail hcellFrame.dataSize
    have htempTail : TempRangeInBounds next.a (tempSrc + 1) count := by
      simpa only [htempEq] using htemp.tail
    have hinitializedTail : TempRangeInitialized next.a (tempSrc + 1) count := by
      simpa only [htempEq] using hinitialized.tail
    have hliveNext : next.a.Live := hcellFrame.live hlive
    rcases ih next (mainDst + 1) (tempSrc + 1) hmainTail htempTail
      hinitializedTail hliveNext with
      ⟨result, hrest, hrestSafe, hrestFrame⟩
    refine ⟨result, ?_, ?_, hcellFrame.trans hrestFrame⟩
    · simp [tempToMainKeysTraced?, TraceResult.bind, hcellResult, hrest]
    · simp only [tempToMainKeysTraced?]
      exact MovementTraceSafe.bind _ _ next hcellResult
        (tempToMainKeyTraced_safe_of_bounds state mainDst tempSrc hmainHead
          htempHead hlive hreadable) hrestSafe

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainValuesPhaseTraced_safe_of_ranges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma tempToMainValuesPhaseTraced_safe_of_ranges
  (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
  (state : MergeState κ ν) (mainDst tempSrc : Int)
  (hmain : SortSlice.RangeInBounds state.data mainDst count)
  (htemp : TempRangeInBounds state.a tempSrc count)
  (hinitialized : TempRangeInitialized state.a tempSrc count)
  (hlive : state.a.Live) :
  ∃ result,
    (tempToMainValuesPhaseTraced? site permit count state mainDst tempSrc).result =
      some result ∧
    MovementTraceSafe
      (tempToMainValuesPhaseTraced? site permit count state mainDst tempSrc) ∧
    MergeMovementFrame state result := by
  induction count generalizing state mainDst tempSrc with
  | zero =>
    refine ⟨state, rfl, MovementTraceSafe.pure state, .refl state⟩
  | succ count ih =>
    have hmainHead := hmain.head
    have htempHead := htemp.head
    have hreadable := hinitialized.head
    rcases tempToMainCell_eq_some_of_bounds state mainDst tempSrc hmainHead
      hreadable with ⟨next, hcell⟩
    have hcellFrame := tempToMainCell_frame state next mainDst tempSrc hcell
    have htempEq := tempToMainCell_temp_eq_of_eq_some state next mainDst tempSrc hcell
    have hcellResult :
      (tempToMainValuesTraced? state mainDst tempSrc).result = some next := by
      change (tempToMainValuesTraced? state mainDst tempSrc).erase = some next
      rwa [erase_tempToMainValuesTraced]
    have hmainTail : SortSlice.RangeInBounds next.data (mainDst + 1) count :=
      SortSlice.RangeInBounds.of_size_eq hmain.tail hcellFrame.dataSize
    have htempTail : TempRangeInBounds next.a (tempSrc + 1) count := by
      simpa only [htempEq] using htemp.tail
    have hinitializedTail : TempRangeInitialized next.a (tempSrc + 1) count := by
      simpa only [htempEq] using hinitialized.tail
    have hliveNext : next.a.Live := hcellFrame.live hlive
    rcases ih next (mainDst + 1) (tempSrc + 1) hmainTail htempTail
      hinitializedTail hliveNext with
      ⟨result, hrest, hrestSafe, hrestFrame⟩
    refine ⟨result, ?_, ?_, hcellFrame.trans hrestFrame⟩
    · simp [tempToMainValuesPhaseTraced?, TraceResult.bind, hcellResult, hrest]
    · simp only [tempToMainValuesPhaseTraced?]
      exact MovementTraceSafe.bind _ _ next hcellResult
        (tempToMainValuesTraced_safe_of_bounds state mainDst tempSrc hmainHead
          htempHead hlive hreadable) hrestSafe

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainMemcpyTraced_traceSafe_of_ranges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma tempToMainMemcpyTraced_traceSafe_of_ranges
  (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
  (state : MergeState κ ν) (mainDst tempSrc : Int)
  (hmain : SortSlice.RangeInBounds state.data mainDst count)
  (htemp : TempRangeInBounds state.a tempSrc count)
  (hinitialized : TempRangeInitialized state.a tempSrc count)
  (hlive : state.a.Live) :
  ∃ result,
    (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).result =
      some result ∧
    MovementTraceSafe
      (tempToMainMemcpyTraced? site permit count state mainDst tempSrc) ∧
    MergeMovementFrame state result := by
  rcases tempToMainKeysTraced_safe_of_ranges site permit count state mainDst
    tempSrc hmain htemp hinitialized hlive with
    ⟨keyResult, hkeys, hkeysSafe, hkeysFrame⟩
  cases hmode : state.a.hasValues with
  | false =>
    refine ⟨keyResult, ?_, ?_, hkeysFrame⟩
    · simp [tempToMainMemcpyTraced?, TraceResult.bind, TraceResult.pure,
      hkeys, hmode]
    · unfold tempToMainMemcpyTraced?
      apply MovementTraceSafe.bind _ _ keyResult hkeys hkeysSafe
      simp only [hmode, Bool.false_eq]
      exact MovementTraceSafe.pure keyResult
  | true =>
    rcases tempToMainValuesPhaseTraced_safe_of_ranges site permit count state
      mainDst tempSrc hmain htemp hinitialized hlive with
      ⟨valuesResult, hvalues, hvaluesSafe, hvaluesFrame⟩
    refine ⟨valuesResult, ?_, ?_, hvaluesFrame⟩
    · simp [tempToMainMemcpyTraced?, TraceResult.bind, hkeys, hmode, hvalues]
    · unfold tempToMainMemcpyTraced?
      apply MovementTraceSafe.bind _ _ keyResult hkeys hkeysSafe
      simpa only [hmode, Bool.true_eq, ↓reduceIte] using hvaluesSafe

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempMemcpyTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainToTempMemcpyTraced_safe
  {site : MergeMemcpySite}
  {permit : site.MainToTempPermit}
  {count : Nat}
  {state : MergeState κ ν}
  {tempDst mainSrc : Int}
-- given
  (htemp : TempRangeInBounds state.a tempDst count)
  (hmain : SortSlice.RangeInBounds state.data mainSrc count)
  (hlive : state.a.Live) :
-- imply
  ∃ result, (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).result = some result ∧ MovementTraceSafe (mainToTempMemcpyTraced? site permit count state tempDst mainSrc) ∧ MergeMovementFrame state result :=
-- proof
  mainToTempMemcpyTraced_traceSafe_of_ranges site permit count state tempDst
    mainSrc htemp hmain hlive

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainMemcpyTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tempToMainMemcpyTraced_safe
  {site : MergeMemcpySite}
  {permit : site.TempToMainPermit}
  {count : Nat}
  {state : MergeState κ ν}
  {mainDst tempSrc : Int}
-- given
  (hmain : SortSlice.RangeInBounds state.data mainDst count)
  (htemp : TempRangeInBounds state.a tempSrc count)
  (hinitialized : TempRangeInitialized state.a tempSrc count)
  (hlive : state.a.Live) :
-- imply
  ∃ result, (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).result = some result ∧ MovementTraceSafe (tempToMainMemcpyTraced? site permit count state mainDst tempSrc) ∧ MergeMovementFrame state result :=
-- proof
  tempToMainMemcpyTraced_traceSafe_of_ranges site permit count state mainDst
    tempSrc hmain htemp hinitialized hlive

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempCell_read_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainToTempCell_read_eq_some
  {state result : MergeState κ ν}
  {tempDst mainSrc : Int}
-- given
  (hcopy : mainToTempCell? state tempDst mainSrc = some result) :
-- imply
  ∃ entry, state.data.read? mainSrc = some entry ∧ mergeTempRead? result.a tempDst = some entry := by
-- proof
  obtain ⟨entry, hread, htail⟩ := Option.bind_eq_some_iff.mp hcopy
  obtain ⟨storage, hwrite, hfinal⟩ := Option.bind_eq_some_iff.mp htail
  change some { state with a := storage } = some result at hfinal
  injection hfinal with hfinal
  subst result
  exact ⟨entry, hread,
    mergeTempWrite_read_self_of_eq_some state.a storage tempDst entry hwrite⟩

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempCell_read_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainToTempCell_read_of_ne
  {state result : MergeState κ ν}
  {tempDst mainSrc other : Int}
-- given
  (hcopy : mainToTempCell? state tempDst mainSrc = some result)
  (hne : other ≠ tempDst) :
-- imply
  mergeTempRead? result.a other = mergeTempRead? state.a other := by
-- proof
  obtain ⟨entry, hread, htail⟩ := Option.bind_eq_some_iff.mp hcopy
  obtain ⟨storage, hwrite, hfinal⟩ := Option.bind_eq_some_iff.mp htail
  change some { state with a := storage } = some result at hfinal
  injection hfinal with hfinal
  subst result
  exact mergeTempWrite_read_ne_of_eq_some state.a storage tempDst other entry
    hwrite hne

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempMemcpy_read_before_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainToTempMemcpy_read_before_of_eq_some
  {count : Nat}
  {state result : MergeState κ ν}
  {tempDst mainSrc other : Int}
-- given
  (hcopy : mainToTempMemcpy? count state tempDst mainSrc = some result)
  (hother : other < tempDst) :
-- imply
  mergeTempRead? result.a other = mergeTempRead? state.a other := by
-- proof
  induction count generalizing state tempDst mainSrc with
  | zero =>
    simp only [mainToTempMemcpy?, Option.some.injEq] at hcopy
    subst result
    rfl
  | succ count ih =>
    simp only [mainToTempMemcpy?, bind, Option.bind] at hcopy
    split at hcopy <;> try contradiction
    rename_i next hhead
    have htail := ih next (tempDst + 1) (mainSrc + 1) hcopy (by omega)
    exact htail.trans
      (mainToTempCell_read_of_ne state next tempDst mainSrc other hhead
        (by omega))

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempMemcpy_valuesMode_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainToTempMemcpy_valuesMode_of_eq_some
  {count : Nat}
  {state result : MergeState κ ν}
  {tempDst mainSrc : Int}
-- given
  (hmode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
  (hcopy : mainToTempMemcpy? count state tempDst mainSrc = some result) :
-- imply
  TempRangeValuesMode result.a tempDst count := by
-- proof
  induction count generalizing state tempDst mainSrc with
  | zero =>
    intro offset hoffset
    omega
  | succ count ih =>
    simp only [mainToTempMemcpy?, bind, Option.bind] at hcopy
    split at hcopy <;> try contradiction
    rename_i next hhead
    have hheadFrame := mainToTempCell_frame state next tempDst mainSrc hhead
    have hdataEq := mainToTempCell_data_eq_of_eq_some state next tempDst mainSrc hhead
    have hmodeNext :
      SortSlice.ValuesModeInvariant next.a.hasValues next.data := by
      simpa only [hheadFrame.tempValuesMode, hdataEq] using hmode
    have htailMode := ih next (tempDst + 1) (mainSrc + 1) hmodeNext hcopy
    intro offset hoffset
    cases offset with
    | zero =>
      rcases mainToTempCell_read_eq_some state next tempDst mainSrc hhead with
        ⟨entry, hread, htempRead⟩
      have hpreserved := mainToTempMemcpy_read_before_of_eq_some count next
        result (tempDst + 1) (mainSrc + 1) tempDst hcopy (by omega)
      have hfinalRead : mergeTempRead? result.a tempDst = some entry :=
        hpreserved.trans htempRead
      refine ⟨entry, ?_, ?_⟩
      · rw [erase_mergeTempRead]
        have hzero : tempDst + Int.ofNat 0 = tempDst := by
          simp [Int.ofNat_eq_natCast]
        rwa [hzero]
      · have hentryMode := hmode.read_matches_of_eq_some hread
        simpa only [hheadFrame.tempValuesMode,
          (mainToTempMemcpy_frame count next result (tempDst + 1)
            (mainSrc + 1) hcopy).tempValuesMode] using hentryMode
    | succ offset =>
      obtain ⟨entry, hread, hentryMode⟩ := htailMode offset (by omega)
      refine ⟨entry, ?_, hentryMode⟩
      have hindex : tempDst + Int.ofNat (offset + 1) =
        tempDst + 1 + Int.ofNat offset := by
        simp [Int.ofNat_eq_natCast, add_left_comm, add_comm]
      simpa only [hindex] using hread

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempMemcpy_data_eq_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainToTempMemcpy_data_eq_of_eq_some
  {count : Nat}
  {state result : MergeState κ ν}
  {tempDst mainSrc : Int}
-- given
  (hcopy : mainToTempMemcpy? count state tempDst mainSrc = some result) :
-- imply
  result.data = state.data := by
-- proof
  induction count generalizing state tempDst mainSrc with
  | zero =>
    simp only [mainToTempMemcpy?, Option.some.injEq] at hcopy
    subst result
    rfl
  | succ count ih =>
    simp only [mainToTempMemcpy?, bind, Option.bind] at hcopy
    split at hcopy <;> try contradiction
    rename_i next hhead
    exact (ih next (tempDst + 1) (mainSrc + 1) hcopy).trans
      (mainToTempCell_data_eq_of_eq_some state next tempDst mainSrc hhead)

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainCell_valuesMode_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tempToMainCell_valuesMode_of_eq_some
  {state result : MergeState κ ν}
  {mainDst tempSrc : Int}
-- given
  (hmainMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
  (hentryMode : ∀ entry, mergeTempRead? state.a tempSrc = some entry → SortSlice.EntryMatchesValuesMode state.a.hasValues entry)
  (hcopy : tempToMainCell? state mainDst tempSrc = some result) :
-- imply
  SortSlice.ValuesModeInvariant result.a.hasValues result.data := by
-- proof
  obtain ⟨entry, hread, htail⟩ := Option.bind_eq_some_iff.mp hcopy
  obtain ⟨data, hwrite, hfinal⟩ := Option.bind_eq_some_iff.mp htail
  change some { state with data := data } = some result at hfinal
  injection hfinal with hfinal
  subst result
  exact hmainMode.write_preserved_of_eq_some (hentryMode entry hread) hwrite

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainMemcpy_temp_eq_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tempToMainMemcpy_temp_eq_of_eq_some
  {count : Nat}
  {state result : MergeState κ ν}
  {mainDst tempSrc : Int}
-- given
  (hcopy : tempToMainMemcpy? count state mainDst tempSrc = some result) :
-- imply
  result.a = state.a := by
-- proof
  induction count generalizing state mainDst tempSrc with
  | zero =>
    simp only [tempToMainMemcpy?, Option.some.injEq] at hcopy
    subst result
    rfl
  | succ count ih =>
    simp only [tempToMainMemcpy?, bind, Option.bind] at hcopy
    split at hcopy <;> try contradiction
    rename_i next hhead
    exact (ih next (mainDst + 1) (tempSrc + 1) hcopy).trans
      (tempToMainCell_temp_eq_of_eq_some state next mainDst tempSrc hhead)

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainMemcpy_valuesMode_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tempToMainMemcpy_valuesMode_of_eq_some
  {count : Nat}
  {state result : MergeState κ ν}
  {mainDst tempSrc : Int}
-- given
  (hmainMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
  (htempMode : TempRangeValuesMode state.a tempSrc count)
  (hcopy : tempToMainMemcpy? count state mainDst tempSrc = some result) :
-- imply
  SortSlice.ValuesModeInvariant result.a.hasValues result.data := by
-- proof
  induction count generalizing state mainDst tempSrc with
  | zero =>
    simp only [tempToMainMemcpy?, Option.some.injEq] at hcopy
    subst result
    exact hmainMode
  | succ count ih =>
    simp only [tempToMainMemcpy?, bind, Option.bind] at hcopy
    split at hcopy <;> try contradiction
    rename_i next hhead
    obtain ⟨entry, hread, hentryMode⟩ := htempMode.head
    have hentry : mergeTempRead? state.a tempSrc = some entry := by
      exact hread
    have hmodeNext := tempToMainCell_valuesMode_of_eq_some state next mainDst
      tempSrc hmainMode (fun other hother => by
        rw [hentry] at hother
        injection hother with hother
        subst other
        exact hentryMode) hhead
    have htempEq := tempToMainCell_temp_eq_of_eq_some state next mainDst tempSrc hhead
    have htailMode : TempRangeValuesMode next.a (tempSrc + 1) count := by
      simpa only [htempEq] using htempMode.tail
    exact ih next (mainDst + 1) (tempSrc + 1) hmodeNext htailMode hcopy

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempMemcpyTraced_phase_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainToTempMemcpyTraced_phase_order
  {site : MergeMemcpySite}
  {permit : site.MainToTempPermit}
  {count : Nat}
  {state : MergeState κ ν}
  {tempDst mainSrc : Int}
-- given
  (hkeys : ∃ keyResult, (mainToTempKeysTraced? site permit count state tempDst mainSrc).result = some keyResult) :
-- imply
  (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).trace.accesses = (mainToTempKeysTraced? site permit count state tempDst mainSrc).trace.accesses ++ (if state.a.hasValues then (mainToTempValuesPhaseTraced? site permit count state tempDst mainSrc).trace.accesses else []) := by
-- proof
  obtain ⟨keyResult, hkeys⟩ := hkeys
  unfold mainToTempMemcpyTraced?
  rw [TraceResult.trace_bind, hkeys]
  cases hmode : state.a.hasValues <;>
    simp [AccessTrace.compose, TraceResult.pure, AccessTrace.empty]

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainMemcpyTraced_phase_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tempToMainMemcpyTraced_phase_order
  {site : MergeMemcpySite}
  {permit : site.TempToMainPermit}
  {count : Nat}
  {state : MergeState κ ν}
  {mainDst tempSrc : Int}
-- given
  (hkeys : ∃ keyResult, (tempToMainKeysTraced? site permit count state mainDst tempSrc).result = some keyResult) :
-- imply
  (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).trace.accesses = (tempToMainKeysTraced? site permit count state mainDst tempSrc).trace.accesses ++ (if state.a.hasValues then (tempToMainValuesPhaseTraced? site permit count state mainDst tempSrc).trace.accesses else []) := by
-- proof
  obtain ⟨keyResult, hkeys⟩ := hkeys
  unfold tempToMainMemcpyTraced?
  rw [TraceResult.trace_bind, hkeys]
  cases hmode : state.a.hasValues <;>
    simp [AccessTrace.compose, TraceResult.pure, AccessTrace.empty]

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempKeyTraced_events](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma mainToTempKeyTraced_events
  (state : MergeState κ ν) (tempDst mainSrc : Int)
  (hmain : SortSlice.IndexInBounds state.data mainSrc) :
  (mainToTempKeyTraced? state tempDst mainSrc).trace.HasAccess
    .read .inputKeys ∧
    (mainToTempKeyTraced? state tempDst mainSrc).trace.HasTempAccess .write := by
  rcases SortSlice.read_eq_some_of_indexInBounds state.data mainSrc hmain with
    ⟨entry, hread⟩
  have hreadTraced :
    (TraceResult.sortSliceKeysRead? state.data mainSrc).result = some entry := by
    change (TraceResult.sortSliceKeysRead? state.data mainSrc).erase = some entry
    simpa using hread
  unfold mainToTempKeyTraced?
  rw [TraceResult.trace_bind, hreadTraced]
  constructor
  · apply AccessTrace.HasAccess.compose_left
    refine ⟨AccessEvent.mk .read .inputKeys mainSrc state.data.entries.size,
      ?_, rfl, rfl⟩
    simp [TraceResult.trace_sortSliceKeysRead, AccessTrace.singletonAccess]
  · apply AccessTrace.HasTempAccess.compose_right
    change (TraceResult.tempPayloadWrite? state.a tempDst entry).trace.HasTempAccess
      .write
    refine ⟨state.a.backing, ?_⟩
    refine ⟨AccessEvent.mk .write (.tempPayload state.a.backing) tempDst
      state.a.cells.size, ?_, rfl, rfl⟩
    simp [TraceResult.trace_tempPayloadWrite, AccessTrace.singletonAccess]

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempValuesTraced_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma mainToTempValuesTraced_event
  (state : MergeState κ ν) (tempDst mainSrc : Int)
  (hmain : SortSlice.IndexInBounds state.data mainSrc) :
  (mainToTempValuesTraced? state tempDst mainSrc).trace.HasAccess
    .read .synchronizedValues := by
  rcases SortSlice.read_eq_some_of_indexInBounds state.data mainSrc hmain with
    ⟨entry, hread⟩
  have hreadTraced :
    (TraceResult.sortSliceValuesRead? state.data mainSrc).result = some entry := by
    change (TraceResult.sortSliceValuesRead? state.data mainSrc).erase = some entry
    simpa using hread
  unfold mainToTempValuesTraced?
  rw [TraceResult.trace_bind, hreadTraced]
  apply AccessTrace.HasAccess.compose_left
  refine ⟨AccessEvent.mk .read .synchronizedValues mainSrc
    state.data.entries.size, ?_, rfl, rfl⟩
  simp [TraceResult.trace_sortSliceValuesRead, AccessTrace.singletonAccess]

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainKeyTraced_events](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma tempToMainKeyTraced_events
  (state : MergeState κ ν) (mainDst tempSrc : Int)
  (hreadable : ∃ entry, mergeTempRead? state.a tempSrc = some entry) :
  (tempToMainKeyTraced? state mainDst tempSrc).trace.HasTempAccess .read ∧
    (tempToMainKeyTraced? state mainDst tempSrc).trace.HasAccess
      .write .inputKeys := by
  obtain ⟨entry, hread⟩ := hreadable
  have hreadTraced :
    (TraceResult.tempPayloadRead? state.a tempSrc).result = some entry := by
    change (TraceResult.tempPayloadRead? state.a tempSrc).erase = some entry
    rwa [erase_mergeTempRead]
  unfold tempToMainKeyTraced?
  rw [TraceResult.trace_bind, hreadTraced]
  constructor
  · apply AccessTrace.HasTempAccess.compose_left
    refine ⟨state.a.backing, ?_⟩
    refine ⟨AccessEvent.mk .read (.tempPayload state.a.backing) tempSrc
      state.a.cells.size, ?_, rfl, rfl⟩
    simp [TraceResult.trace_tempPayloadRead, AccessTrace.singletonAccess]
  · apply AccessTrace.HasAccess.compose_right
    change (TraceResult.sortSliceKeysWrite? state.data mainDst entry).trace.HasAccess
      .write .inputKeys
    refine ⟨AccessEvent.mk .write .inputKeys mainDst state.data.entries.size,
      ?_, rfl, rfl⟩
    simp [TraceResult.trace_sortSliceKeysWrite, AccessTrace.singletonAccess]

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainValuesTraced_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma tempToMainValuesTraced_event
  (state : MergeState κ ν) (mainDst tempSrc : Int)
  (hreadable : ∃ entry, mergeTempRead? state.a tempSrc = some entry) :
  (tempToMainValuesTraced? state mainDst tempSrc).trace.HasAccess
    .write .synchronizedValues := by
  obtain ⟨entry, hread⟩ := hreadable
  have hreadTraced :
    (TraceResult.tempPayloadRead? state.a tempSrc).result = some entry := by
    change (TraceResult.tempPayloadRead? state.a tempSrc).erase = some entry
    rwa [erase_mergeTempRead]
  unfold tempToMainValuesTraced?
  rw [TraceResult.trace_bind, hreadTraced]
  apply AccessTrace.HasAccess.compose_right
  change (TraceResult.sortSliceValuesWrite? state.data mainDst entry).trace.HasAccess
    .write .synchronizedValues
  refine ⟨AccessEvent.mk .write .synchronizedValues mainDst state.data.entries.size,
    ?_, rfl, rfl⟩
  simp [TraceResult.trace_sortSliceValuesWrite, AccessTrace.singletonAccess]

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempKeysTraced_first_events](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma mainToTempKeysTraced_first_events
  (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
  (state : MergeState κ ν) (tempDst mainSrc : Int)
  (htemp : TempRangeInBounds state.a tempDst (count + 1))
  (hmain : SortSlice.RangeInBounds state.data mainSrc (count + 1)) :
  (mainToTempKeysTraced? site permit (count + 1) state tempDst mainSrc).trace.HasAccess
    .read .inputKeys ∧
    (mainToTempKeysTraced? site permit (count + 1) state tempDst
      mainSrc).trace.HasTempAccess .write := by
  rcases mainToTempCell_eq_some_of_bounds state tempDst mainSrc htemp.head
    hmain.head with ⟨next, hcell⟩
  have hcellResult :
    (mainToTempKeyTraced? state tempDst mainSrc).result = some next := by
    change (mainToTempKeyTraced? state tempDst mainSrc).erase = some next
    rwa [erase_mainToTempKeyTraced]
  simp only [mainToTempKeysTraced?, TraceResult.trace_bind, hcellResult]
  rcases mainToTempKeyTraced_events state tempDst mainSrc hmain.head with
    ⟨hread, hwrite⟩
  exact ⟨hread.compose_left, hwrite.compose_left⟩

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempValuesPhaseTraced_first_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma mainToTempValuesPhaseTraced_first_event
  (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
  (state : MergeState κ ν) (tempDst mainSrc : Int)
  (htemp : TempRangeInBounds state.a tempDst (count + 1))
  (hmain : SortSlice.RangeInBounds state.data mainSrc (count + 1)) :
  (mainToTempValuesPhaseTraced? site permit (count + 1) state tempDst
    mainSrc).trace.HasAccess .read .synchronizedValues := by
  rcases mainToTempCell_eq_some_of_bounds state tempDst mainSrc htemp.head
    hmain.head with ⟨next, hcell⟩
  have hcellResult :
    (mainToTempValuesTraced? state tempDst mainSrc).result = some next := by
    change (mainToTempValuesTraced? state tempDst mainSrc).erase = some next
    rwa [erase_mainToTempValuesTraced]
  simp only [mainToTempValuesPhaseTraced?, TraceResult.trace_bind, hcellResult]
  exact (mainToTempValuesTraced_event state tempDst mainSrc hmain.head).compose_left

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempMemcpyTraced_events](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainToTempMemcpyTraced_events
  {site : MergeMemcpySite}
  {permit : site.MainToTempPermit}
  {count : Nat}
  {state : MergeState κ ν}
  {tempDst mainSrc : Int}
-- given
  (htemp : TempRangeInBounds state.a tempDst (count + 1))
  (hmain : SortSlice.RangeInBounds state.data mainSrc (count + 1))
  (hlive : state.a.Live) :
-- imply
  (mainToTempMemcpyTraced? site permit (count + 1) state tempDst mainSrc).trace.HasAccess .read .inputKeys ∧ (mainToTempMemcpyTraced? site permit (count + 1) state tempDst mainSrc).trace.HasTempAccess .write ∧ (state.a.hasValues = true → (mainToTempMemcpyTraced? site permit (count + 1) state tempDst mainSrc).trace.HasAccess .read .synchronizedValues) := by
-- proof
  rcases mainToTempKeysTraced_safe_of_ranges site permit (count + 1) state
    tempDst mainSrc htemp hmain hlive with ⟨keyResult, hkeys, _, _⟩
  have htrace :
    (mainToTempMemcpyTraced? site permit (count + 1) state tempDst
      mainSrc).trace =
    (mainToTempKeysTraced? site permit (count + 1) state tempDst
      mainSrc).trace.compose
      (if state.a.hasValues then
        (mainToTempValuesPhaseTraced? site permit (count + 1) state tempDst
          mainSrc).trace
      else (TraceResult.pure keyResult).trace) := by
    cases hmode : state.a.hasValues <;>
      simp [mainToTempMemcpyTraced?, TraceResult.trace_bind, hkeys, hmode]
  rw [htrace]
  rcases mainToTempKeysTraced_first_events site permit count state tempDst
    mainSrc htemp hmain with ⟨hread, hwrite⟩
  refine ⟨hread.compose_left, hwrite.compose_left, ?_⟩
  intro hmode
  simp only [hmode, ↓reduceIte]
  exact (mainToTempValuesPhaseTraced_first_event site permit count state tempDst
    mainSrc htemp hmain).compose_right

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainKeysTraced_first_events](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma tempToMainKeysTraced_first_events
  (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
  (state : MergeState κ ν) (mainDst tempSrc : Int)
  (hmain : SortSlice.RangeInBounds state.data mainDst (count + 1))
  (hinitialized : TempRangeInitialized state.a tempSrc (count + 1)) :
  (tempToMainKeysTraced? site permit (count + 1) state mainDst
    tempSrc).trace.HasTempAccess .read ∧
    (tempToMainKeysTraced? site permit (count + 1) state mainDst
      tempSrc).trace.HasAccess .write .inputKeys := by
  have hreadable := hinitialized.head
  rcases tempToMainCell_eq_some_of_bounds state mainDst tempSrc hmain.head
    hreadable with ⟨next, hcell⟩
  have hcellResult :
    (tempToMainKeyTraced? state mainDst tempSrc).result = some next := by
    change (tempToMainKeyTraced? state mainDst tempSrc).erase = some next
    rwa [erase_tempToMainKeyTraced]
  simp only [tempToMainKeysTraced?, TraceResult.trace_bind, hcellResult]
  rcases tempToMainKeyTraced_events state mainDst tempSrc hreadable with
    ⟨hread, hwrite⟩
  exact ⟨hread.compose_left, hwrite.compose_left⟩

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainValuesPhaseTraced_first_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma tempToMainValuesPhaseTraced_first_event
  (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
  (state : MergeState κ ν) (mainDst tempSrc : Int)
  (hmain : SortSlice.RangeInBounds state.data mainDst (count + 1))
  (hinitialized : TempRangeInitialized state.a tempSrc (count + 1)) :
  (tempToMainValuesPhaseTraced? site permit (count + 1) state mainDst
    tempSrc).trace.HasAccess .write .synchronizedValues := by
  have hreadable := hinitialized.head
  rcases tempToMainCell_eq_some_of_bounds state mainDst tempSrc hmain.head
    hreadable with ⟨next, hcell⟩
  have hcellResult :
    (tempToMainValuesTraced? state mainDst tempSrc).result = some next := by
    change (tempToMainValuesTraced? state mainDst tempSrc).erase = some next
    rwa [erase_tempToMainValuesTraced]
  simp only [tempToMainValuesPhaseTraced?, TraceResult.trace_bind, hcellResult]
  exact (tempToMainValuesTraced_event state mainDst tempSrc hreadable).compose_left

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainMemcpyTraced_events](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tempToMainMemcpyTraced_events
  {site : MergeMemcpySite}
  {permit : site.TempToMainPermit}
  {count : Nat}
  {state : MergeState κ ν}
  {mainDst tempSrc : Int}
-- given
  (hmain : SortSlice.RangeInBounds state.data mainDst (count + 1))
  (htemp : TempRangeInBounds state.a tempSrc (count + 1))
  (hinitialized : TempRangeInitialized state.a tempSrc (count + 1))
  (hlive : state.a.Live) :
-- imply
  (tempToMainMemcpyTraced? site permit (count + 1) state mainDst tempSrc).trace.HasTempAccess .read ∧ (tempToMainMemcpyTraced? site permit (count + 1) state mainDst tempSrc).trace.HasAccess .write .inputKeys ∧ (state.a.hasValues = true → (tempToMainMemcpyTraced? site permit (count + 1) state mainDst tempSrc).trace.HasAccess .write .synchronizedValues) := by
-- proof
  rcases tempToMainKeysTraced_safe_of_ranges site permit (count + 1) state
    mainDst tempSrc hmain htemp hinitialized hlive with
    ⟨keyResult, hkeys, _, _⟩
  have htrace :
    (tempToMainMemcpyTraced? site permit (count + 1) state mainDst
      tempSrc).trace =
    (tempToMainKeysTraced? site permit (count + 1) state mainDst
      tempSrc).trace.compose
      (if state.a.hasValues then
        (tempToMainValuesPhaseTraced? site permit (count + 1) state mainDst
          tempSrc).trace
      else (TraceResult.pure keyResult).trace) := by
    cases hmode : state.a.hasValues <;>
      simp [tempToMainMemcpyTraced?, TraceResult.trace_bind, hkeys, hmode]
  rw [htrace]
  rcases tempToMainKeysTraced_first_events site permit count state mainDst
    tempSrc hmain hinitialized with ⟨hread, hwrite⟩
  refine ⟨hread.compose_left, hwrite.compose_left, ?_⟩
  intro hmode
  simp only [hmode, ↓reduceIte]
  exact (tempToMainValuesPhaseTraced_first_event site permit count state mainDst
    tempSrc hmain hinitialized).compose_right

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempMemcpyTraced_post](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainToTempMemcpyTraced_post
  {site : MergeMemcpySite}
  {permit : site.MainToTempPermit}
  {count : Nat}
  {state : MergeState κ ν}
  {tempDst mainSrc : Int}
-- given
  (htemp : TempRangeInBounds state.a tempDst count)
  (hmain : SortSlice.RangeInBounds state.data mainSrc count)
  (hinvariant : TempStorageInv state.a state.alloced)
  (hlive : state.a.Live)
  (hmode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
-- imply
  ∃ result, MainToTempMemcpyPost site permit count state result tempDst mainSrc := by
-- proof
  rcases mainToTempMemcpyTraced_safe site permit count state tempDst mainSrc
    htemp hmain hlive with ⟨result, hresult, htraceSafe, hframe⟩
  have hcopy : mainToTempMemcpy? count state tempDst mainSrc = some result := by
    rwa [← erase_mainToTempMemcpyTraced site permit count state tempDst mainSrc]
  have htempMode := mainToTempMemcpy_valuesMode_of_eq_some count state result
    tempDst mainSrc hmode hcopy
  have hdataEq := mainToTempMemcpy_data_eq_of_eq_some count state result tempDst
    mainSrc hcopy
  have hresultMode :
    SortSlice.ValuesModeInvariant result.a.hasValues result.data := by
    simpa only [hframe.tempValuesMode, hdataEq] using hmode
  have hkeys : ∃ keyResult,
    (mainToTempKeysTraced? site permit count state tempDst mainSrc).result =
      some keyResult := by
    refine ⟨result, ?_⟩
    change (mainToTempKeysTraced? site permit count state tempDst mainSrc).erase =
      some result
    rwa [erase_mainToTempKeysTraced]
  have hphase := mainToTempMemcpyTraced_phase_order site permit count state tempDst
    mainSrc hkeys
  refine ⟨result, ?_⟩
  refine
    { success := hresult
      traceSafe := htraceSafe
      exactErasure := erase_mainToTempMemcpyTraced site permit count state tempDst mainSrc
      frame := hframe
      tempInvariant := hframe.tempStorageInv hinvariant
      tempLive := hframe.live hlive
      valuesMode := hresultMode
      initialized := htempMode.initialized
      tempValuesMode := htempMode
      provenance := permit.distinctBacking
      provenanceContract := mergeMemcpyCallsiteProvenance
      phaseOrder := hphase
      inputKeyEvent := ?_
      tempWriteEvent := ?_
      synchronizedValuesEvent := ?_
      nonempty := ?_ }
  · intro hpositive
    cases count with
    | zero => omega
    | succ tail =>
      exact (mainToTempMemcpyTraced_events site permit tail state tempDst
        mainSrc htemp hmain hlive).1
  · intro hpositive
    cases count with
    | zero => omega
    | succ tail =>
      exact (mainToTempMemcpyTraced_events site permit tail state tempDst
        mainSrc htemp hmain hlive).2.1
  · intro hpositive hvalues
    cases count with
    | zero => omega
    | succ tail =>
      exact (mainToTempMemcpyTraced_events site permit tail state tempDst
        mainSrc htemp hmain hlive).2.2 hvalues
  · intro hpositive
    apply AccessTrace.HasAccess.accesses_ne_nil
    cases count with
    | zero => omega
    | succ tail =>
      exact (mainToTempMemcpyTraced_events site permit tail state tempDst
        mainSrc htemp hmain hlive).1

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainMemcpyTraced_post](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma tempToMainMemcpyTraced_post
  {site : MergeMemcpySite}
  {permit : site.TempToMainPermit}
  {count : Nat}
  {state : MergeState κ ν}
  {mainDst tempSrc : Int}
-- given
  (hmain : SortSlice.RangeInBounds state.data mainDst count)
  (htemp : TempRangeInBounds state.a tempSrc count)
  (htempMode : TempRangeValuesMode state.a tempSrc count)
  (hinvariant : TempStorageInv state.a state.alloced)
  (hlive : state.a.Live)
  (hmainMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
-- imply
  ∃ result, TempToMainMemcpyPost site permit count state result mainDst tempSrc := by
-- proof
  rcases tempToMainMemcpyTraced_safe site permit count state mainDst tempSrc
    hmain htemp htempMode.initialized hlive with
    ⟨result, hresult, htraceSafe, hframe⟩
  have hcopy : tempToMainMemcpy? count state mainDst tempSrc = some result := by
    rwa [← erase_tempToMainMemcpyTraced site permit count state mainDst tempSrc]
  have htempEq := tempToMainMemcpy_temp_eq_of_eq_some count state result mainDst
    tempSrc hcopy
  have hresultMode := tempToMainMemcpy_valuesMode_of_eq_some count state result
    mainDst tempSrc hmainMode htempMode hcopy
  have hresultTempMode : TempRangeValuesMode result.a tempSrc count := by
    simpa only [htempEq] using htempMode
  have hkeys : ∃ keyResult,
    (tempToMainKeysTraced? site permit count state mainDst tempSrc).result =
      some keyResult := by
    refine ⟨result, ?_⟩
    change (tempToMainKeysTraced? site permit count state mainDst tempSrc).erase =
      some result
    rwa [erase_tempToMainKeysTraced]
  have hphase := tempToMainMemcpyTraced_phase_order site permit count state mainDst
    tempSrc hkeys
  refine ⟨result, ?_⟩
  refine
    { success := hresult
      traceSafe := htraceSafe
      exactErasure := erase_tempToMainMemcpyTraced site permit count state mainDst tempSrc
      frame := hframe
      tempInvariant := hframe.tempStorageInv hinvariant
      tempLive := hframe.live hlive
      valuesMode := hresultMode
      initialized := hresultTempMode.initialized
      tempValuesMode := hresultTempMode
      provenance := permit.distinctBacking
      provenanceContract := mergeMemcpyCallsiteProvenance
      phaseOrder := hphase
      tempReadEvent := ?_
      inputKeyEvent := ?_
      synchronizedValuesEvent := ?_
      nonempty := ?_ }
  · intro hpositive
    cases count with
    | zero => omega
    | succ tail =>
      exact (tempToMainMemcpyTraced_events site permit tail state mainDst
        tempSrc hmain htemp htempMode.initialized hlive).1
  · intro hpositive
    cases count with
    | zero => omega
    | succ tail =>
      exact (tempToMainMemcpyTraced_events site permit tail state mainDst
        tempSrc hmain htemp htempMode.initialized hlive).2.1
  · intro hpositive hvalues
    cases count with
    | zero => omega
    | succ tail =>
      exact (tempToMainMemcpyTraced_events site permit tail state mainDst
        tempSrc hmain htemp htempMode.initialized hlive).2.2 hvalues
  · intro hpositive
    apply AccessTrace.HasAccess.accesses_ne_nil
    cases count with
    | zero => omega
    | succ tail =>
      exact (tempToMainMemcpyTraced_events site permit tail state mainDst
        tempSrc hmain htemp htempMode.initialized hlive).2.1

end CPythonListsort

namespace CPythonListsort

/--
[keyRead_tempLive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma keyRead_tempLive (slice : SortSlice κ ν) (index : Int) :
  MovementTempLive (TraceResult.sortSliceKeysRead? slice index) := by
  simp [MovementTempLive, TraceResult.trace_sortSliceKeysRead,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort

namespace CPythonListsort

/--
[valuesRead_tempLive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma valuesRead_tempLive (slice : SortSlice κ ν) (index : Int) :
  MovementTempLive (TraceResult.sortSliceValuesRead? slice index) := by
  simp [MovementTempLive, TraceResult.trace_sortSliceValuesRead,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort

namespace CPythonListsort

/--
[keyWrite_tempLive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma keyWrite_tempLive (slice : SortSlice κ ν) (index : Int)
  (entry : SortSliceEntry κ ν) :
  MovementTempLive (TraceResult.sortSliceKeysWrite? slice index entry) := by
  simp [MovementTempLive, TraceResult.trace_sortSliceKeysWrite,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort

namespace CPythonListsort

/--
[valuesWrite_tempLive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma valuesWrite_tempLive (slice : SortSlice κ ν) (index : Int)
  (entry : SortSliceEntry κ ν) :
  MovementTempLive (TraceResult.sortSliceValuesWrite? slice index entry) := by
  simp [MovementTempLive, TraceResult.trace_sortSliceValuesWrite,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort

namespace CPythonListsort

/--
[copyKeysFrom_tempLive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma copyKeysFrom_tempLive (destination source : SortSlice κ ν)
  (dst src : Int) :
  MovementTempLive (SortSlice.copyKeysFromTraced? destination source dst src) := by
  apply MovementTempLive.bind
  · exact keyRead_tempLive source src
  · intro entry
    exact keyWrite_tempLive destination dst entry

end CPythonListsort

namespace CPythonListsort

/--
[copyValuesFrom_tempLive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma copyValuesFrom_tempLive (destination source : SortSlice κ ν)
  (dst src : Int) :
  MovementTempLive (SortSlice.copyValuesFromTraced? destination source dst src) := by
  apply MovementTempLive.bind
  · exact valuesRead_tempLive source src
  · intro entry
    exact valuesWrite_tempLive destination dst entry

end CPythonListsort

namespace CPythonListsort

/--
[memmoveForwardKeys_tempLive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma memmoveForwardKeys_tempLive (count : Nat)
  (slice : SortSlice κ ν) (dst src : Int) :
  MovementTempLive (SortSlice.memmoveForwardKeysTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact MovementTempLive.pure slice
  | succ count ih =>
    apply MovementTempLive.bind
    · exact copyKeysFrom_tempLive slice slice dst src
    · intro updated
      exact ih updated (dst + 1) (src + 1)

end CPythonListsort

namespace CPythonListsort

/--
[memmoveForwardValues_tempLive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma memmoveForwardValues_tempLive (count : Nat)
  (slice : SortSlice κ ν) (dst src : Int) :
  MovementTempLive (SortSlice.memmoveForwardValuesTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact MovementTempLive.pure slice
  | succ count ih =>
    apply MovementTempLive.bind
    · exact copyValuesFrom_tempLive slice slice dst src
    · intro updated
      exact ih updated (dst + 1) (src + 1)

end CPythonListsort

namespace CPythonListsort

/--
[memmoveBackwardKeys_tempLive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma memmoveBackwardKeys_tempLive (count : Nat)
  (slice : SortSlice κ ν) (dst src : Int) :
  MovementTempLive (SortSlice.memmoveBackwardKeysTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact MovementTempLive.pure slice
  | succ count ih =>
    apply MovementTempLive.bind
    · exact copyKeysFrom_tempLive slice slice (dst + Int.ofNat count)
      (src + Int.ofNat count)
    · intro updated
      exact ih updated dst src

end CPythonListsort

namespace CPythonListsort

/--
[memmoveBackwardValues_tempLive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma memmoveBackwardValues_tempLive (count : Nat)
  (slice : SortSlice κ ν) (dst src : Int) :
  MovementTempLive (SortSlice.memmoveBackwardValuesTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact MovementTempLive.pure slice
  | succ count ih =>
    apply MovementTempLive.bind
    · exact copyValuesFrom_tempLive slice slice (dst + Int.ofNat count)
      (src + Int.ofNat count)
    · intro updated
      exact ih updated dst src

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceMemmove_tempLive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma sortSliceMemmove_tempLive (valuesPresent : Bool)
  (slice : SortSlice κ ν) (dst src : Int) (count : Nat) :
  MovementTempLive
    (SortSlice.memmoveTraced? valuesPresent slice dst src count) := by
  cases hdirection : SortSlice.memmoveDirection dst src with
  | forward =>
    simp only [SortSlice.memmoveTraced?, hdirection]
    apply MovementTempLive.bind
    · exact memmoveForwardKeys_tempLive count slice dst src
    · intro keyResult
      cases hvalues : valuesPresent with
      | false => simp only [Bool.false_eq]
        exact MovementTempLive.pure keyResult
      | true => simp only [↓reduceIte]
        exact memmoveForwardValues_tempLive count slice dst src
  | backward =>
    simp only [SortSlice.memmoveTraced?, hdirection]
    apply MovementTempLive.bind
    · exact memmoveBackwardKeys_tempLive count slice dst src
    · intro keyResult
      cases hvalues : valuesPresent with
      | false => simp only [Bool.false_eq]
        exact MovementTempLive.pure keyResult
      | true => simp only [↓reduceIte]
        exact memmoveBackwardValues_tempLive count slice dst src

end CPythonListsort

namespace CPythonListsort

/--
[erase_mainDataCopyDecrTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma erase_mainDataCopyDecrTraced
  {state : MergeState κ ν}
  {dst src : Int} :
-- imply
  (mainDataCopyDecrTraced? state dst src).erase = mergeHiCopyDataDecr? state dst src := by
-- proof
  rw [mainDataCopyDecrTraced?, TraceResult.erase_map,
    SortSlice.erase_copyDecrTraced]
  cases hcopy : state.data.copyDecr? dst src <;>
    simp [mergeHiCopyDataDecr?, hcopy]

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceCopyFrom_accessOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma sortSliceCopyFrom_accessOnly (valuesPresent : Bool)
  (destination source : SortSlice κ ν) (dst src : Int) :
  MovementAccessOnly
    (SortSlice.copyFromTraced? valuesPresent destination source dst src) := by
  apply MovementAccessOnly.bind
  · exact copyKeysFrom_accessOnly destination source dst src
  · intro keyResult
    cases valuesPresent with
    | false => exact MovementAccessOnly.pure keyResult
    | true => exact copyValuesFrom_accessOnly destination source dst src

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceCopyFrom_tempLive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma sortSliceCopyFrom_tempLive (valuesPresent : Bool)
  (destination source : SortSlice κ ν) (dst src : Int) :
  MovementTempLive
    (SortSlice.copyFromTraced? valuesPresent destination source dst src) := by
  apply MovementTempLive.bind
  · exact copyKeysFrom_tempLive destination source dst src
  · intro keyResult
    cases valuesPresent with
    | false => exact MovementTempLive.pure keyResult
    | true => exact copyValuesFrom_tempLive destination source dst src

end CPythonListsort

namespace CPythonListsort

/--
[mainDataCopyDecrTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainDataCopyDecrTraced_safe
  {state : MergeState κ ν}
  {dst src : Int}
-- given
  (hinvariant : TempStorageInv state.a state.alloced)
  (hlive : state.a.Live)
  (hmode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
  (hdst : SortSlice.IndexInBounds state.data dst)
  (hsrc : SortSlice.IndexInBounds state.data src) :
-- imply
  ∃ result, MainDataCopyDecrPost state dst src result := by
-- proof
  rcases SortSlice.copyFromTraced_mode_safe state.a.hasValues state.data
    state.data dst src hmode hmode hdst hsrc with
    ⟨updated, hcopy, hbounds, hsize, hupdatedMode⟩
  let copied : SortSlice.CursorResult κ ν :=
    { slice := updated, dst := dst - 1, src := src - 1 }
  have hcopied :
    (SortSlice.copyDecrTraced? state.a.hasValues state.data dst src).result =
      some copied := by
    simp [SortSlice.copyDecrTraced?, SortSlice.copyFromDecrTraced?,
      TraceResult.map, hcopy, copied]
  let result : MergeHiDataCursorResult κ ν :=
    { state := { state with data := updated }
      dst := dst - 1
      src := src - 1 }
  have hresult :
    (mainDataCopyDecrTraced? state dst src).result = some result := by
    simp [mainDataCopyDecrTraced?, TraceResult.map, hcopied, result, copied]
  have haccessOnly := sortSliceCopyFrom_accessOnly state.a.hasValues state.data
    state.data dst src
  have htempAccessLive := sortSliceCopyFrom_tempLive state.a.hasValues state.data
    state.data dst src
  have htraceSafe : MovementTraceSafe (mainDataCopyDecrTraced? state dst src) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [mainDataCopyDecrTraced?, SortSlice.copyDecrTraced?,
      SortSlice.copyFromDecrTraced?, TraceResult.map,
      MovementAccessOnly] using haccessOnly.1
    · simpa [mainDataCopyDecrTraced?, SortSlice.copyDecrTraced?,
      SortSlice.copyFromDecrTraced?, TraceResult.map,
      MovementAccessOnly] using haccessOnly.2
    · simpa [mainDataCopyDecrTraced?, SortSlice.copyDecrTraced?,
      SortSlice.copyFromDecrTraced?, TraceResult.map] using hbounds
    · simpa [mainDataCopyDecrTraced?, SortSlice.copyDecrTraced?,
      SortSlice.copyFromDecrTraced?, TraceResult.map,
      MovementTempLive] using htempAccessLive
  have hframe : MergeMovementFrame state result.state := by
    dsimp [result]
    constructor <;> try rfl
    exact hsize
  have hresultMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data := by
    exact hupdatedMode
  exact ⟨result,
    { success := hresult
      traceSafe := htraceSafe
      exactErasure := erase_mainDataCopyDecrTraced state dst src
      frame := hframe
      tempInvariant := hframe.tempStorageInv hinvariant
      tempLive := hframe.live hlive
      valuesMode := hresultMode
      dstDecrement := by rfl
      srcDecrement := by rfl }⟩

end CPythonListsort

namespace CPythonListsort

/--
[mainDataMemmoveTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
lemma mainDataMemmoveTraced_safe
  {state : MergeState κ ν}
  {dst src : Int}
  {count : Nat}
-- given
  (hinvariant : TempStorageInv state.a state.alloced)
  (hlive : state.a.Live)
  (hmode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
  (hdst : SortSlice.RangeInBounds state.data dst count)
  (hsrc : SortSlice.RangeInBounds state.data src count) :
-- imply
  ∃ result, MainDataMemmovePost state result dst src count := by
-- proof
  rcases SortSlice.memmoveTraced_mode_safe state.a.hasValues state.data dst src
    count hmode hdst hsrc with ⟨data, hdataResult, hbounds, hsize, hdataMode⟩
  let result : MergeState κ ν := { state with data := data }
  have hresult :
    (mainDataMemmoveTraced? state dst src count).result = some result := by
    simp [mainDataMemmoveTraced?, TraceResult.map, hdataResult, result]
  have hframe := mainDataMemmoveTraced_frame state result dst src count hresult
  have haccessOnly := mainDataMemmoveTraced_accessOnly state dst src count
  have htempAccessLive :
    (mainDataMemmoveTraced? state dst src count).trace.tempPayloadAccessesLive := by
    exact sortSliceMemmove_tempLive state.a.hasValues state.data dst src count
  have htraceSafe :
    MovementTraceSafe (mainDataMemmoveTraced? state dst src count) :=
    ⟨haccessOnly.1, haccessOnly.2, hbounds, htempAccessLive⟩
  have hresultMode :
    SortSlice.ValuesModeInvariant result.a.hasValues result.data := by
    exact hdataMode
  refine ⟨result,
    { success := hresult
      traceSafe := htraceSafe
      exactErasure := erase_mainDataMemmoveTraced state dst src count
      frame := hframe
      tempInvariant := hframe.tempStorageInv hinvariant
      tempLive := hframe.live hlive
      valuesMode := hresultMode
      phaseOrder := ?_ }⟩
  exact SortSlice.memmoveTraced_phase_order state.a.hasValues state.data dst src
    count hdst hsrc

end CPythonListsort

/--
[distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma distinct_eq
  {site : MergeMemcpySite} :
-- imply
  site.backings.Distinct := by
-- proof
  apply CPythonListsort.MergeMemcpySite.distinct site

/--
[initialized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma initialized_eq
  {storage : TempStorage κ ν}
  {start : Int}
  {count : Nat}
-- given
  (h : TempRangeValuesMode storage start count) :
-- imply
  TempRangeInitialized storage start count := by
-- proof
  apply CPythonListsort.TempRangeValuesMode.initialized h

/--
[bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma bind_eq_2
  {current : TraceResult α}
  {next : α → TraceResult β}
  {value : α}
-- given
  (hresult : current.result = some value)
  (hcurrent : MovementTraceSafe current)
  (hnext : MovementTraceSafe (next value)) :
-- imply
  MovementTraceSafe (current.bind next) := by
-- proof
  apply CPythonListsort.MovementTraceSafe.bind current next value hresult hcurrent hnext

/--
[pure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma pure_eq_3
  {value : α} :
-- imply
  MovementTempLive (TraceResult.pure value) := by
-- proof
  apply CPythonListsort.MovementTempLive.pure value

/--
[map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma map_eq_3
  {current : TraceResult α}
  {transform : α → β}
-- given
  (h : MovementTempLive current) :
-- imply
  MovementTempLive (current.map transform) := by
-- proof
  apply CPythonListsort.MovementTempLive.map current transform h

/--
[bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean)
-/
@[path]
private lemma bind_eq_3
  {current : TraceResult α}
  {next : α → TraceResult β}
-- given
  (hcurrent : MovementTempLive current)
  (hnext : ∀ value, MovementTempLive (next value)) :
-- imply
  MovementTempLive (current.bind next) := by
-- proof
  apply CPythonListsort.MovementTempLive.bind current next hcurrent hnext


-- created on 2026-10-23
