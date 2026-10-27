"""Write the three scoped metadata files after the formal freeze and DOI reservation."""
from copy import deepcopy
from pathlib import Path
import json
import yaml

ROOT = Path(__file__).resolve().parents[1]
AUTHOR = "Juan Pablo Traverso Gianini"
validation = json.loads((ROOT / "publication/assembly/VALIDATION.json").read_text())
assert validation["status"] == "PASS"
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
        "status": {"sorry_count": 0, "sorry_in_definitions": 0, "axioms": [],
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
                    {"title": "Steiner triple systems having a prescribed number of triples in common", "authors": ["C. C. Lindner", "A. Rosa"], "id": "doi:10.4153/CJM-1975-122-4", "type": "paper", "relationship": "background", "note": "Classical intersection literature, read together with its 1978 corrigendum."},
                    {"title": "Steiner triple systems having a prescribed number of triples in common (corrigendum)", "authors": ["C. C. Lindner", "A. Rosa"], "id": "doi:10.4153/CJM-1978-077-9", "type": "paper", "relationship": "background", "location": "Canadian Journal of Mathematics 30 (1978), p. 896"}],
        "fidelity": "Completion sparsity concerns the maximum (r−1)-degree of the covered r-edges; the forbidden partial system need not be sparse. The additional crossing guarantee in completion is restricted to forbidden blocks whose r-edges avoid the prescribed covered edges. The spectrum chooses both systems and supplies an initial interval k ≤ c n^r, not a complete spectrum. Disjoint mates have no common blocks; classical orthogonality is not asserted. Polynomial error bounds count partial parallel classes or schedule rounds, and do not assert perfect classes or a deficit bound for every round. The external polynomial colouring theorem assumes a maximum-degree bound, a polynomial codegree bound and an exponential edge-count cap; all are verified before application. The closed endpoints have no external theorem hypotheses. The original conditional consumers remain unchanged."},
}
for name, profile in profiles.items():
    metadata = deepcopy(base)
    metadata["project"].update(name=profile["title"], description=profile["description"])
    metadata["sources"] = deepcopy(profile["sources"])
    metadata["fidelity"] = {"divergences": profile["fidelity"]}
    config = json.loads((ROOT / "Palomar" / (name + ".comparator.json")).read_text())
    metadata["alignment"] = {"statements": [{"source": "See the source-qualified endpoint table in the formal companion.", "lean": theorem, "module": config["challenge_module"], "status": "proved"} for theorem in config["theorem_names"]]}
    if name == "ResearchNote":
        metadata["related_formalizations"] = [
            {"id": "https://github.com/jtraverso/pippenger-spencer/tree/b19273396d369332fb489fe07e61e27c9e7f9233", "relationship": "builds-on", "note": "Pinned three-file polynomial-colouring proof cut, sharing nineteen source-identical matching modules with the Nash–Williams dependency."},
            {"id": "https://github.com/jtraverso/nash-williams-lean/tree/2603197abdbf0a600ec663f6f046f70fbd209d4a", "relationship": "builds-on", "note": "The proved large-order decomposition endpoint via Papers I–II; source graph theorem remains attributed to Delcourt–Postle."}]
    target = ROOT / "Palomar" / name / "formalization.yaml"
    target.parent.mkdir(exist_ok=True)
    target.write_text(yaml.safe_dump(metadata, sort_keys=False, allow_unicode=True, width=88), encoding="utf-8", newline="\n")
    print(target.relative_to(ROOT))
