/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean -/

import Mathlib
import Def.CPythonListsort.Code.Transcription.SortSlice.Part6
/-!
# `sortslice` model and movement primitives

CPython stores keys and optional payload values in parallel pointer arrays.
The Lean model stores their observable pairing as one entry, so every movement
primitive moves a key and its payload atomically.  Integer indices replace raw
pointers.  Failed bounds checks are explicit through `Option`; later safety
proofs establish that transcribed calls return `some`.

`memmove` carries explicit backing provenance.  On one shared store it chooses
its traversal direction from the overlap geometry: a rightward overlapping
move copies from the end, while a leftward move copies from the beginning, so
unread source entries are never overwritten.  A distinct backing instead uses
the source-language's forward two-store copy order, even when its contents
happen to equal the destination.  `memcpy` uses the same provenance distinction
but rejects overlapping same-backing ranges.
-/


namespace CPythonListsort

universe u v

namespace SortSlice

/-- Equal contents do not collapse explicit distinct-backing provenance. -/
example :
    memcpy? 4 overlapExample (.distinctBacking overlapExample) 0 0 =
      some overlapExample := by
  decide

/-- A positive exact self-copy overlaps and is therefore not a `memcpy`. -/
example : memcpy? 1 overlapExample .sameBacking 0 0 = none := by
  decide

/-- The rejection is range-based, not limited to the one-cell boundary. -/
example : memcpy? 2 overlapExample .sameBacking 1 1 = none := by
  decide

/-- Same-backing ranges may meet at the source-to-destination endpoint. -/
example :
    memcpy? 2 overlapExample .sameBacking 2 0 =
      some
        { entries :=
            #[{ key := 1, value := some 10 },
              { key := 2, value := some 20 },
              { key := 1, value := some 10 },
              { key := 2, value := some 20 }] } := by
  decide

/-- Same-backing ranges may also meet in the opposite order. -/
example :
    memcpy? 2 overlapExample .sameBacking 0 2 =
      some
        { entries :=
            #[{ key := 3, value := some 30 },
              { key := 4, value := some 40 },
              { key := 3, value := some 30 },
              { key := 4, value := some 40 }] } := by
  decide

/-- An empty copy admits equal one-past cursors on a shared backing. -/
example : memcpy? 0 overlapExample .sameBacking 4 4 = some overlapExample := by
  decide

/-- A rightward overlapping move retains the unread entries and their payloads. -/
example :
    overlapExample.memmove? 1 0 3 =
      some
        { entries :=
            #[{ key := 1, value := some 10 },
              { key := 1, value := some 10 },
              { key := 2, value := some 20 },
              { key := 3, value := some 30 }] } := by
  decide

/-- Equal contents do not turn explicit distinct provenance into aliasing. -/
example :
    memmoveFrom? overlapExample (.distinctBacking overlapExample) 0 0 4 =
      some overlapExample := by
  decide

/-- The general same-backing API retains backward-safe rightward overlap. -/
example :
    memmoveFrom? overlapExample .sameBacking 1 0 3 =
      some
        { entries :=
            #[{ key := 1, value := some 10 },
              { key := 1, value := some 10 },
              { key := 2, value := some 20 },
              { key := 3, value := some 30 }] } := by
  decide

end SortSlice
end CPythonListsort
