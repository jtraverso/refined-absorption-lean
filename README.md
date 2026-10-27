# Refined absorption in Lean

Lean formalization directed by Juan Pablo Traverso Gianini, with AI assistance from
Harmonic's Aristotle and OpenAI Codex. This development studies the following sources:

| Source | Authors | Formalization scope |
| --- | --- | --- |
| [Refined Absorption: A New Proof of the Existence Conjecture](https://arxiv.org/abs/2402.17855) | Michelle Delcourt and Luke Postle | Refined absorbers and refiners, minimum-degree existence, and the statements 2.8, 6.2 and 6.3 |
| [Refined Absorption: A New Proof of the Existence Conjecture and its Applications to Extremal and Probabilistic Design Theory](https://arxiv.org/abs/2510.19978) | Luke Postle | The refined absorption framework and its interfaces, with documented statement-fidelity qualifications |

The library also contains completion, embedding, counting, packing, colouring and
prescribed-intersection consequences. These are extensions of the formal library;
their presence does not establish mathematical priority over the literature.

## Migration status

The complete returned development has been migrated from Lean 4.28.0 to the version
used by the related Palomar registrations:

- Lean `4.35.0-rc3`;
- Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`;
- 300 original Lean sources, including the returned check scripts.

On 27 October 2026 all 301 current sources compiled locally: the 300 retained
originals and one shared Mathlib import module. The eight original check modules
ran 354 axiom queries, all reporting only Lean's foundational axioms. The source
audit records 56 adjusted original files, no deletions, no textual changes to
declaration headers, and no active `sorry`, `admit` or project axiom declarations.
These are source-preservation checks, not a cross-version kernel equivalence test.

The immutable input is Aristotle task `8717482d-2162-428e-9db4-f6de76bc61fe` in project
`88ab8568-7432-483b-897c-4163327799b2`. Original source hashes are recorded in
`provenance/source-baseline.json`; returned summaries are historical evidence, not
independent build certificates. Local migration output is kept under `migration/`.

The evidence is frozen in `migration/VALIDATION.json`, `migration/rc3-checks/` and
`migration/VERIFICATION.txt`. A clean standard Lake build and independent registry
verification remain separate gates. There is no Palomar registration or published
research note for this development yet.

## Build

The portable project configuration pins the dependency revision:

```sh
lake exe cache get
lake build
```

The local migration additionally uses `tools/build_local.py` to compile every source
against an existing verified dependency cache without modifying that cache. This is
separate evidence from a standard clean Lake build. Its machine-local configuration
is ignored by Git; it is not a public dependency specification.

The default Lake targets include both `RequestProject` and `checks`, so the portable
configuration also selects the eight check modules. This does not assert that a
single aggregate source module imports or re-exports every declaration.

## Statement fidelity and external interfaces

- All previously returned declarations are retained. Migration repairs must preserve
  their mathematical statements and record changes to proof scripts.
- The survey's literal global embedding interpretation has a formal counterexample
  in `RequestProject/FaithfulSurvey2025/Embedding.lean`. The proved placement variant
  and its relationship to the printed definition must be explained explicitly in
  any paper-level or Palomar description.
- Quantitative almost-resolution and Nash–Williams scheduling currently expose
  external theorem hypotheses. A future integrated endpoint must import pinned
  proofs and discharge those hypotheses before being called unconditional.
- `steiner_orthogonal_mate` asserts bounded cross-intersections and no common blocks;
  it does not establish classical orthogonality of Steiner systems.

## Repository and publication plan

This is a separate development from the
[Nash–Williams Papers I–II release](https://github.com/jtraverso/nash-williams-triangle-decompositions-release).
The latter remains the publication home of those triangle-decomposition papers.
A cross-link can connect the projects after this migration is verified.

The intended later publication is a research note about formalization, statement
fidelity, reusable proof interfaces and selected extensions. The papers above remain
works of their original authors. Palomar records exact mathematical declarations at
an immutable commit; a research note supplies context and is not itself a substitute
for the Challenge/Solution comparison.

The recommended Palomar layout is one source repository with separate small
interfaces for the original article, the survey's proved scope, and selected note
extensions, if these need separate configurations. No entry should advertise that a
literal statement is proved when the library instead proves an adapted variant.

Publication and registration follow the completed migration and the review of the
research note. Neither action is performed by this migration step.
