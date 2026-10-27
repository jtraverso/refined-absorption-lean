"""Write the canonical joint metadata and retained narrower profiles."""
from copy import deepcopy
from pathlib import Path
import json
import re
import yaml

ROOT = Path(__file__).resolve().parents[1]
AUTHOR = "Juan Pablo Traverso Gianini"
validation = json.loads((ROOT / "publication/assembly/VALIDATION.json").read_text())
assert validation["status"] == "PASS"
used_axioms = sorted({axiom.strip()
    for check in validation["axiom_checks"]
    for group in re.findall(r"depends on axioms:\s*\[(.*?)\]", (ROOT / check["log"]).read_text(encoding="utf-8"), re.S)
    for axiom in group.split(",") if axiom.strip()})
assert set(used_axioms) <= set(validation["permitted_axioms"])
reservation = json.loads((ROOT / "publication/zenodo/note-reservation.json").read_text())
DOI = reservation["reserved_doi"]
assert DOI == "10.5281/zenodo." + str(reservation["id"])

article = {"title": "Refined Absorption: A New Proof of the Existence Conjecture",
           "authors": ["Michelle Delcourt", "Luke Postle"], "id": "doi:10.48550/arXiv.2402.17855",
           "type": "paper", "relationship": "formalizes", "location": "arXiv:2402.17855v1 (2024)",
           "author_endorsement": "not-contacted"}
survey = {"title": "Refined Absorption: A New Proof of the Existence Conjecture and Its Applications to Extremal and Probabilistic Design Theory",
          "authors": ["Luke Postle"], "id": "doi:10.1137/25M1805977", "type": "paper",
          "relationship": "adapts", "location": "ICM 2026, Volume 6, pp. 212–231; statement baseline arXiv:2510.19978v1",
          "note": "The core absorption and existence endpoints are proved. The global embedding statement is distinguished from its proved piecewise variant and a counterexample to the literal global conclusion.",
          "author_endorsement": "not-contacted"}
note = {"title": "Formalizing refined absorption: proof interfaces and consequences", "authors": [AUTHOR],
        "id": "doi:" + DOI, "type": "paper", "relationship": "formalizes", "location": "Research note, version 1.0 (2026)",
        "note": "Verified consequences and interface analysis; historical priority for every corollary is not claimed.",
        "license": "CC-BY-4.0", "author_endorsement": "participated"}
base = {"version": "v0.4", "project": {"authors": [AUTHOR], "license": "Apache-2.0", "responsible_maintainers": [AUTHOR]},
        "classification": {"arxiv": ["math.CO"], "msc2020": ["05B05", "05B07", "05C15", "05C70"]},
        "automation": {"methods": [
            {"method": "agent", "models": ["Aristotle (Harmonic)"], "framework": "Aristotle",
             "tool_setup": "Under the author's direction, explored constructions, developed and formalized proofs, and checked extensions. Its contribution was not limited to translation of finished proofs."},
            {"method": "agent", "models": ["Codex (OpenAI)"], "framework": "Codex",
             "tool_setup": "Migrated the retained development, assembled pinned proved inputs, exposed ambient independence in an additive 6.2 interface, reviewed source fidelity and consequences, prepared the manuscripts and reproducibility evidence, and performed the internal audit."}],
            "notes": "Human authorship and responsibility remain with the author. Exact formal source revisions and build records are supplied in the repository."},
        "review": {"status": "self-assessed", "notes": "Internal source-fidelity and mathematical review by Codex under the author's direction; see publication/MATHEMATICAL_REVIEW_NOTES.md and publication/AUDIT.md. No independent human or separate-agent peer review is claimed."},
        "status": {"sorry_count": 0, "sorry_in_definitions": 0, "axioms": used_axioms,
                   "note": "The proof development has no project axiom or proof hole. The standalone Challenge files deliberately use by sorry; their Solutions import the actual proofs. Endpoint queries use only propext, Classical.choice and Quot.sound."}}
profiles = {
    "Article2024": {
        "title": "Refined absorption: refiners, reserve matchings and compatible decompositions",
        "description": "Formalization of the refined omni-absorber and refiner theorems of Delcourt–Postle, the reserve-matching theorem for labelled multi-hypergraphs, and the dense decomposition theorem with compatibility against a prescribed packing. The compatible absorber endpoint explicitly keeps the entire old vertex set independent, including isolated labels. The original support-based endpoint is retained. The construction follows the refined absorption framework and gives an explicit deduction of compatible absorbers from dense decomposition results. Constants and order thresholds are existential.",
        "sources": [article, {**survey, "relationship": "background"}, {**note, "relationship": "background"}],
        "fidelity": "The 2024 article's theorem numbers are used. Hypergraphs in the 1.7 and 1.11 interfaces carry explicit vertex sets, including isolated vertices. Refined families retain bounded edge usage, bounded member size and the separate refinement-degree bound. The 2.8 endpoint allows labelled parallel copies and does not add disjointness of the named sets A and B. The added 6.2 endpoint retains all previous conclusions and additionally makes the whole old ambient set independent; it does not require the absorber to avoid old vertices altogether. Theorems quantify over ordinary finite objects in universe 0. This is a selection of principal statements, not a claim that every statement of the article is compared."},
    "Survey2025": {
        "title": "Refined absorption: design existence and the piecewise embedding interface",
        "description": "Formalization of the refined efficient omni-absorber framework and existence of simple designs for every fixed q > r ≥ 2 and index λ ≥ 1 at all sufficiently large admissible orders. The development separately defines global injectivity, injectivity on individual pieces and distinctness of new edges in supergraph embeddings. It proves the piecewise embedding variant used by the formal constructions and a counterexample to the literal global embedding conclusion in the survey. The distinction is part of the formal statement, rather than an additional hypothesis left implicit.",
        "sources": [survey, article, {**note, "relationship": "background"},
                    {"title": "Erdős meets Nash-Williams", "authors": ["Michelle Delcourt", "Cicely (Cece) Henderson", "Thomas Lesgourgues", "Luke Postle"], "id": "doi:10.48550/arXiv.2507.23624", "type": "paper", "relationship": "background", "location": "arXiv:2507.23624v1, Appendix B", "note": "The survey's cited proof reference was checked; the formal counterexample covers all old vertices, so it is unaffected by conventions about unused old vertices."}],
        "fidelity": "The statement baseline is arXiv:2510.19978v1; the DOI identifies its published ICM 2026 edition. Definitions 3.6–3.7 and Lemma 3.8 were also checked in that edition. The literal global embedding conclusion is refuted, not proved. The proved replacement permits separate injective maps on pieces with distinct images of new edges. The existence endpoint produces a finite set of blocks for every fixed λ ≥ 1, without repeated blocks. General high-girth and other applications announced in the survey are outside this compared scope. Thresholds are existential."},
    "ResearchNote": {
        "title": "Formalizing refined absorption: completion, intersections and polynomial schedules",
        "description": "Formal consequences of refined absorption: completion of a sparse partial Steiner system while avoiding an arbitrary forbidden partial system, prescribed sparse intersections, embedding a finite partial system as the exact intersection of two systems at every sufficiently large admissible order, and an initial intersection spectrum of order n^r. For fixed q > r ≥ 2, every sufficiently large Steiner system also admits a partition into partial parallel classes using at most R + R^(1−γ) classes, where R is its point degree. At the exact Nash–Williams minimum-degree threshold, triangle decompositions admit schedules with at most Δ(G)/2 + (Δ(G)/2)^(1−γ) rounds of vertex-disjoint triangles. The colouring and decomposition inputs are discharged by pinned proved theorems.",
        "sources": [note, {**article, "relationship": "adapts"}, {**survey, "relationship": "background"},
                    {"title": "Pseudorandom hypergraph matchings", "authors": ["Stefan Ehard", "Stefan Glock", "Felix Joos"], "id": "doi:10.1017/S0963548320000280", "type": "paper", "relationship": "adapts", "note": "The polynomial colouring input is derived via Theorem 1.2 in the pinned Pippenger–Spencer development."},
                    {"title": "Asymptotic behavior of the chromatic index for hypergraphs", "authors": ["Nicholas Pippenger", "Joel Spencer"], "id": "doi:10.1016/0097-3165(89)90074-5", "type": "paper", "relationship": "background"},
                    {"title": "A Proof of Nash-Williams' Conjecture", "authors": ["Michelle Delcourt", "Luke Postle"], "id": "doi:10.48550/arXiv.2606.11178", "type": "paper", "relationship": "adapts"},
                    {"title": "Triangle decompositions I: Formalizing the Nash–Williams theorem in Lean", "authors": [AUTHOR], "id": "doi:10.5281/zenodo.23428173", "type": "paper", "relationship": "background", "note": "Documents the proved decomposition endpoint reused by the scheduling assembly."},
                    {"title": "Triangle decompositions II: Robust absorption for typed triangles", "authors": [AUTHOR], "id": "doi:10.5281/zenodo.23502224", "type": "paper", "relationship": "background", "note": "Documents the proved replacement inputs used by that decomposition endpoint."},
                    {"title": "Steiner triple systems having a prescribed number of triples in common", "authors": ["C. C. Lindner", "A. Rosa"], "id": "doi:10.4153/CJM-1975-122-4", "type": "paper", "relationship": "background", "note": "Classical intersection literature, read together with its 1978 corrigendum."},
                    {"title": "Steiner triple systems having a prescribed number of triples in common (corrigendum)", "authors": ["C. C. Lindner", "A. Rosa"], "id": "doi:10.4153/CJM-1978-077-9", "type": "paper", "relationship": "background", "location": "Canadian Journal of Mathematics 30 (1978), p. 896"}],
        "fidelity": "Completion sparsity concerns the maximum (r−1)-degree of the covered r-edges; the forbidden partial system need not be sparse. The additional crossing guarantee in completion is restricted to forbidden blocks whose r-edges avoid the prescribed covered edges. The spectrum chooses both systems and supplies an initial interval k ≤ c n^r, not a complete spectrum. Disjoint mates have no common blocks; classical orthogonality is not asserted. Polynomial error bounds count partial parallel classes or schedule rounds, and do not assert perfect classes or a deficit bound for every round. The external polynomial colouring theorem assumes a maximum-degree bound, a polynomial codegree bound and an exponential edge-count cap; all are verified before application. The closed endpoints have no external theorem hypotheses. The original conditional consumers remain unchanged."},
}
profiles["Unified"] = {
    "title": "Formalizing refined absorption: proof interfaces and consequences",
    "description": "One assembled Lean formalization of principal refined absorption results and their consequences. The selected results include refined omni-absorbers and refiners, labelled reserve matchings, dense compatible decompositions, an additive compatible-absorber interface retaining independence of the entire old ambient vertex set, and existence of simple designs for every fixed q > r ≥ 2 and index λ ≥ 1 at all sufficiently large admissible orders. The literal global embedding conclusion of the survey is refuted separately from a proved piecewise replacement. The research-note endpoints give completion avoiding an arbitrary forbidden partial Steiner system, sparse prescribed and finite embedded exact intersections, an initial polynomial intersection interval, and polynomial excess in partial parallel classes and Nash–Williams schedule rounds. Both external inputs are supplied by pinned proved theorems. The single comparison selects eighteen declarations from the existing aggregate proof root.",
    "sources": [article, survey, note] +
               deepcopy(profiles["ResearchNote"]["sources"][3:]) +
               [deepcopy(profiles["Survey2025"]["sources"][-1])],
    "fidelity": ("The canonical submission uses Palomar/Unified.comparator.json, "
                 "a standalone Mathlib-only Challenge and the existing "
                 "RefinedAbsorption aggregate root as its Solution. It compares "
                 "all eighteen selected declarations in one entry. The three "
                 "narrower configurations are retained as historical/optional "
                 "views, not three intended submissions. " +
                 " ".join(profiles[key]["fidelity"]
                          for key in ("Article2024", "Survey2025", "ResearchNote"))),
}
locations = {
    "RefinedAbsorption.Faithful2024.theorem_1_7": "Delcourt–Postle, arXiv:2402.17855v1, Theorem 1.7 (refined omni-absorber).",
    "RefinedAbsorption.Faithful2024.theorem_1_11": "Delcourt–Postle, arXiv:2402.17855v1, Theorem 1.11 (refiner, including the family refinement-degree bound).",
    "RefinedAbsorption.Original2024.theorem_6_1": "Delcourt–Postle, arXiv:2402.17855v1, Theorem 6.1 (dense divisible decomposition).",
    "RefinedAbsorption.Pending.theorem_2_8": "Delcourt–Postle, arXiv:2402.17855v1, Theorem 2.8 (labelled multi-hypergraph reserve matching).",
    "RefinedAbsorption.Faithful2024.theorem_6_2_ambient": "Delcourt–Postle, arXiv:2402.17855v1, Theorem 6.2; additive interface explicitly retaining independence of all old ambient vertices.",
    "RefinedAbsorption.Pending.theorem_6_3": "Delcourt–Postle, arXiv:2402.17855v1, Theorem 6.3 (compatible decomposition against a prescribed packing).",
    "RefinedAbsorption.Final.theorem_1_10": "Postle survey, arXiv:2510.19978v1 and ICM 2026 edition, Theorem 1.10 (refined efficient omni-absorber).",
    "RefinedAbsorption.existenceConjecture_proved": "Postle survey, Conjecture 1.1, proved existence statement for every fixed index λ ≥ 1; simple block family.",
    "RefinedAbsorption.Final.existenceConjecture_steiner": "Steiner special case λ = 1 of the survey's Conjecture 1.1.",
    "RefinedAbsorption.FaithfulSurvey2025.not_generalEmbeddingLemmaLiteral": "Counterexample to the global-injection reading of survey Definition 3.7 and Lemma 3.8, both checked in the arXiv and ICM editions. The selected theorem proves its negation.",
    "RefinedAbsorption.FaithfulSurvey2025.generalEmbedding_piecewise": "Proved piecewise replacement for survey Lemma 3.8, with new-edge distinctness; not the printed global-injection conclusion.",
    "RefinedAbsorption.Extensions.steiner_completion_avoiding": "Research note, Section 5, completion avoiding an arbitrary partial Steiner system, derived from article Theorem 6.3.",
    "RefinedAbsorption.Extensions.steiner_intersection_prescribed": "Research note, Section 5, prescribed sparse intersection with a fixed Steiner system.",
    "RefinedAbsorption.Extensions.partialSteiner_intersection_embedding": "Research note, Section 5, exact-intersection embedding at every sufficiently large admissible order.",
    "RefinedAbsorption.Extensions.steiner_intersection_spectrum_poly": "Research note, Section 5, initial intersection interval k ≤ c n^r, choosing both systems.",
    "RefinedAbsorption.Assembly.steiner_quantitatively_almost_resolvable": "Research note, Section 6, polynomial excess in the number of partial parallel classes for every sufficiently large Steiner system.",
    "RefinedAbsorption.Assembly.exists_quantitatively_almost_resolvable_steiner": "Research note, Section 6, existence at all sufficiently large admissible orders, with the same partial-class conclusion.",
    "RefinedAbsorption.Assembly.nash_williams_scheduled_decomposition": "Research note, Section 6, polynomial-round schedule at the exact Nash–Williams minimum-degree threshold.",
}
for name, profile in profiles.items():
    metadata = deepcopy(base)
    metadata["project"].update(name=profile["title"], description=profile["description"])
    metadata["sources"] = deepcopy(profile["sources"])
    metadata["fidelity"] = {"divergences": profile["fidelity"]}
    config = json.loads((ROOT / "Palomar" / (name + ".comparator.json")).read_text())
    metadata["alignment"] = {"statements": [{"source": locations[theorem], "lean": theorem, "module": config["challenge_module"], "status": "proved"} for theorem in config["theorem_names"]]}
    if name in {"ResearchNote", "Unified"}:
        metadata["related_formalizations"] = [
            {"id": "https://github.com/jtraverso/pippenger-spencer/tree/b19273396d369332fb489fe07e61e27c9e7f9233", "relationship": "builds-on", "note": "Pinned three-file polynomial-colouring proof cut, sharing nineteen source-identical matching modules with the Nash–Williams dependency."},
            {"id": "https://github.com/jtraverso/nash-williams-lean/tree/2603197abdbf0a600ec663f6f046f70fbd209d4a", "relationship": "builds-on", "note": "The proved large-order decomposition endpoint via Papers I–II; source graph theorem remains attributed to Delcourt–Postle."}]
    target = ROOT / "Palomar" / name / "formalization.yaml"
    target.parent.mkdir(exist_ok=True)
    target.write_text(yaml.safe_dump(metadata, sort_keys=False, allow_unicode=True, width=88), encoding="utf-8", newline="\n")
    print(target.relative_to(ROOT))
