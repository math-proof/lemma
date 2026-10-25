/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean -/

import Def.CPythonListsort.Code.Assembly.MergeMemcpyProvenance
import Theorem.CPythonListsort.Code.Assembly.MergeTracePrimitives
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

/-- A classified main-to-temporary site, with provenance kept explicit. -/
structure MainToTempPermit (site : MergeMemcpySite) : Prop where
  direction : site.backings =
    { destination := .temporary, source := .main }
  distinctBacking : site.backings.Distinct

/-- A classified temporary-to-main site, with provenance kept explicit. -/
structure TempToMainPermit (site : MergeMemcpySite) : Prop where
  direction : site.backings =
    { destination := .main, source := .temporary }
  distinctBacking : site.backings.Distinct

end MergeMemcpySite
end CPythonListsort
