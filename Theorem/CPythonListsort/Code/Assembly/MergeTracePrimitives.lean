/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean -/

import Def.CPythonListsort.Code.Assembly.MergeMemcpyProvenance
import Def.CPythonListsort.Code.Assembly.MergeTracePrimitives
/-!
# Typed trace support for merge movement

The merge transcriptions keep the main list in `MergeState.data` and the
shorter run in `MergeState.a`.  `SortSlice`'s two-store movement API cannot be
used directly for that pair because temporary storage has a distinct carrier,
an explicit live/released backing state, and possibly-uninitialized cells.

This module supplies the common traced movement layer used by both merge
directions.  Every access goes through a state-derived wrapper from
`AccessTrace`; in particular, callers cannot manufacture the temporary backing
or either extent.  Bulk `memcpy` executors retain a classified call-site tag,
its exact direction, and its distinct-backing certificate at every recursive
call.  Key accesses for the complete range precede the optional synchronized-
values phase, which is selected solely by `state.a.hasValues`.
-/


namespace CPythonListsort

universe u v

open SortSlice

namespace MergeMemcpySite

/-- The exported provenance theorem covers every site in the closed union. -/
theorem distinct (site : MergeMemcpySite) : site.backings.Distinct := by
  cases site with
  | lo site =>
      exact
        (mergeMemcpyCallsiteProvenance (κ := Unit) (ν := Unit))
          |>.mergeLoCallsitesDistinct site
  | hi site =>
      exact
        (mergeMemcpyCallsiteProvenance (κ := Unit) (ν := Unit))
          |>.mergeHiCallsitesDistinct site

end MergeMemcpySite
end CPythonListsort
