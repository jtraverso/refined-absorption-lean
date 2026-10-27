# Repository decision

Use a dedicated repository for refined absorption, and link it from the existing
Nash–Williams release repository after verification.

The existing release repository distributes Papers I and II and their frozen
companions, licences, DOI records and bilingual publication files. The Lean source
repositories for those papers are already separate. Refined absorption has a more
general scope (`q > r`) and its own mathematical sources, fidelity issues and
extensions. Keeping an independent source history avoids making changes to a
published release or coupling unrelated build dependencies.

One new repository can hold the entire migrated library and the later research note.
Within it, separate Comparator configurations can distinguish source-based results
from note extensions. Palomar states that one configuration corresponds to one entry;
several configurations may share the same immutable repository commit. Final entry
boundaries should follow the actual statements and the Challenge size limit, rather
than the number of PDF documents.

The current Palomar minimum is `v4.35.0-rc2`; `v4.35.0-rc3` remains supported and
matches the existing Nash–Williams, typed-absorption and Pippenger–Spencer projects.
The selected Mathlib commit's own toolchain is exactly rc3.

Evidence checked on 26 October 2026:

- <https://palomar-registry.org/how-to-submit>
- <https://github.com/PalomarRegistry/PalomarSubmission/blob/main/toolchains.json>
- <https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md>
- <https://github.com/jtraverso/palomar-formalizations>
- <https://github.com/jtraverso/nash-williams-triangle-decompositions-release>

No public repository, release, registry submission or research-note publication is
created by this decision document. Local work starts in `C:/nw/refined-absorption-lean`.
