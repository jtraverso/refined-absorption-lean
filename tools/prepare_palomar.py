"""Extract standalone Challenge vocabulary without importing the proof library.

Every extracted span is recorded with its source hash. Solution modules import
the real theorems under the same names; they do not import their Challenge.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "Palomar"
OUT.mkdir(exist_ok=True)
spans = []


def read(path):
    return (ROOT / path).read_text(encoding="utf-8")


def take(path, start, end):
    source = read(path)
    a = source.index(start)
    b = source.index(end, a + len(start))
    text = source[a:b].strip()
    spans.append({"source": path, "start_line": source[:a].count("\n") + 1,
                  "end_line": source[:b].count("\n") + 1,
                  "sha256": hashlib.sha256(text.encode()).hexdigest()})
    return text + "\n"


def definition(path, name):
    source = read(path)
    match = re.search(r"^(?:noncomputable )?(?:def|abbrev|structure) " + re.escape(name) + r"\b", source, re.M)
    assert match, (path, name)
    end = source.find("\n\n", match.start())
    assert end > match.start()
    first_line = source[match.start():source.index("\n", match.start())]
    return take(path, first_line, source[end:end+20])


def theorem(path, name):
    source = read(path)
    match = re.search(r"^theorem " + re.escape(name) + r"\b", source, re.M)
    assert match, (path, name)
    end = source.index(":=", match.start())
    return source[match.start():end].rstrip() + " := by sorry\n"


def namespace(name, body):
    return "namespace " + name + "\n" + body + "end " + name + "\n"


basic = take("RefinedAbsorption/Basic.lean", "namespace RefinedAbsorption", "end RefinedAbsorption") + "end RefinedAbsorption\n"
degrees = namespace("RefinedAbsorption", "open Finset\n" +
    definition("RefinedAbsorption/Statements.lean", "MaxDegLE") +
    definition("RefinedAbsorption/Statements.lean", "MinDegGE"))
absorbers = namespace("RefinedAbsorption", "variable {V : Type*} [DecidableEq V]\n" +
    take("RefinedAbsorption/Absorbers.lean", "structure IsAbsorber", "/-- **Booster**"))
designs = namespace("RefinedAbsorption", "variable {V : Type*} [DecidableEq V] [Fintype V]\n" +
    definition("RefinedAbsorption/Designs.lean", "IsDesign") +
    definition("RefinedAbsorption/Designs.lean", "IsSteinerSystem") +
    definition("RefinedAbsorption/Designs.lean", "DesignDivisibility"))
header = """/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in LICENSE.
-/
module
MATHLIB_IMPORTS
@[expose] public section
/-! Standalone statements. The expected `sorry` placeholders occur only in
Challenge modules. Source correspondence: provenance/palomar-extractions.json. -/
""".replace("MATHLIB_IMPORTS", "\n".join(line for line in read("RefinedAbsorption/MathlibImports.lean").splitlines() if line.startswith("public import Mathlib")))

article = basic + degrees + absorbers
article += namespace("RefinedAbsorption", "open Finset\nvariable {U V : Type*} [DecidableEq U] [DecidableEq V]\n" +
    definition("RefinedAbsorption/Absorber17/Maps.lean", "gmap"))
article += namespace("RefinedAbsorption.Original2024",
    definition("RefinedAbsorption/Original2024/Defs.lean", "budget") +
    definition("RefinedAbsorption/Original2024/Defs.lean", "Theorem_6_1_for") +
    definition("RefinedAbsorption/Original2024/Defs.lean", "Theorem_6_1") +
    theorem("RefinedAbsorption/Original2024/MinDegree.lean", "theorem_6_1"))
article += namespace("RefinedAbsorption.Faithful2024", "open Finset\n" +
    definition("RefinedAbsorption/Faithful2024/Defs.lean", "budget") +
    take("RefinedAbsorption/Faithful2024/Defs.lean", "structure HGraph", "end RefinedAbsorption.Faithful2024") +
    take("RefinedAbsorption/Faithful2024/Section2.lean", "variable {V E", "end RefinedAbsorption.Faithful2024") +
    definition("RefinedAbsorption/Faithful2024/Section6.lean", "Theorem_6_2") +
    definition("RefinedAbsorption/Faithful2024/Section6.lean", "Theorem_6_3") +
    theorem("RefinedAbsorption/Faithful2024/Section1.lean", "theorem_1_7") +
    theorem("RefinedAbsorption/Faithful2024/Section1.lean", "theorem_1_11"))
article += namespace("RefinedAbsorption.Pending",
    theorem("RefinedAbsorption/Pending/Theorem28.lean", "theorem_2_8") +
    theorem("RefinedAbsorption/Pending/Theorem62.lean", "theorem_6_2") +
    theorem("RefinedAbsorption/Pending/Theorem63Final.lean", "theorem_6_3"))

survey = basic + degrees + absorbers + designs
survey += namespace("RefinedAbsorption",
    definition("RefinedAbsorption/Statements.lean", "RefinedEfficientOmniAbsorber") +
    definition("RefinedAbsorption/Statements.lean", "ExistenceConjecture") +
    theorem("RefinedAbsorption/Multigraph/Existence.lean", "existenceConjecture_proved") +
    definition("RefinedAbsorption/ExistenceProof.lean", "SteinerExistenceConjecture"))
survey += namespace("RefinedAbsorption.Final", "open RefinedAbsorption\n" +
    theorem("RefinedAbsorption/Final.lean", "theorem_1_10") +
    theorem("RefinedAbsorption/Final.lean", "existenceConjecture_steiner"))
survey += take("RefinedAbsorption/GeneralEmbedding/Defs.lean", "namespace RefinedAbsorption", "open Classical in\n/-- **Lemma 3.8") + "end RefinedAbsorption\n"
embedding = "RefinedAbsorption/FaithfulSurvey2025/Embedding.lean"
survey += namespace("RefinedAbsorption.FaithfulSurvey2025", "open Finset RefinedAbsorption\nvariable {n : ℕ} {ι : Type*} [DecidableEq ι]\n" +
    take(embedding, "def sysMap", "/-- **Global injectivity, unfolded.") +
    "open Classical in\n" + definition(embedding, "jMaxDeg") +
    "open Classical in\n" + definition(embedding, "GeneralEmbeddingLemmaLiteral") +
    "open Classical in\n" + definition(embedding, "GeneralEmbeddingLemmaPiecewise") +
    theorem(embedding, "not_generalEmbeddingLemmaLiteral") +
    theorem(embedding, "generalEmbedding_piecewise"))

note = basic + degrees + designs
note += namespace("RefinedAbsorption.Extensions", "open Finset\nvariable {V : Type*} [DecidableEq V]\n" +
    definition("RefinedAbsorption/Extensions/Partial.lean", "IsPartialSteinerSystem") +
    "end RefinedAbsorption.Extensions\nnamespace RefinedAbsorption.Extensions\nopen Finset\n" +
    "".join(theorem("RefinedAbsorption/Extensions/Intersection.lean", name) for name in
            ["steiner_completion_avoiding", "steiner_intersection_prescribed",
             "partialSteiner_intersection_embedding", "steiner_intersection_spectrum_poly"]))
# The original Assembly header opens Original2024, whose declarations are not used
# in its conclusion; only the DesignDivisibility definition is needed here.
note += take("RefinedAbsorption/Extensions/PolynomialExternal.lean", "namespace RefinedAbsorption.External", "end RefinedAbsorption.External") + "end RefinedAbsorption.External\n"
note += namespace("RefinedAbsorption.Assembly", "open Finset RefinedAbsorption.Extensions\nopen RefinedAbsorption.External RefinedAbsorption.External.NashWilliams\nopen RefinedAbsorption.External.PippengerSpencer\nvariable {q r : ℕ}\n" +
    "".join(theorem("RefinedAbsorption/Assembly.lean", name) for name in
            ["steiner_quantitatively_almost_resolvable", "exists_quantitatively_almost_resolvable_steiner",
             "nash_williams_scheduled_decomposition"]))

projects = {
    "Article2024": (article, ["RefinedAbsorption.Faithful2024.theorem_1_7", "RefinedAbsorption.Faithful2024.theorem_1_11", "RefinedAbsorption.Original2024.theorem_6_1", "RefinedAbsorption.Pending.theorem_2_8", "RefinedAbsorption.Pending.theorem_6_2", "RefinedAbsorption.Pending.theorem_6_3"]),
    "Survey2025": (survey, ["RefinedAbsorption.Final.theorem_1_10", "RefinedAbsorption.existenceConjecture_proved", "RefinedAbsorption.Final.existenceConjecture_steiner", "RefinedAbsorption.FaithfulSurvey2025.not_generalEmbeddingLemmaLiteral", "RefinedAbsorption.FaithfulSurvey2025.generalEmbedding_piecewise"]),
    "ResearchNote": (note, ["RefinedAbsorption.Extensions." + name for name in ["steiner_completion_avoiding", "steiner_intersection_prescribed", "partialSteiner_intersection_embedding", "steiner_intersection_spectrum_poly"]] + ["RefinedAbsorption.Assembly." + name for name in ["steiner_quantitatively_almost_resolvable", "exists_quantitatively_almost_resolvable_steiner", "nash_williams_scheduled_decomposition"]]),
}
solution_imports = {
    "Article2024": ["Faithful2024.Section1", "Original2024.MinDegree", "Pending.Theorem28", "Pending.Theorem62"],
    "Survey2025": ["Multigraph.Existence", "FaithfulSurvey2025.Embedding"],
    "ResearchNote": ["Extensions.Intersection", "Assembly"],
}
for name, (body, names) in projects.items():
    challenge = header + body
    assert len(challenge.splitlines()) <= 1000 and len(challenge.encode()) <= 102400
    (OUT / (name + "Challenge.lean")).write_text(challenge, encoding="utf-8", newline="\n")
    solution = "module\n" + "\n".join("public import RefinedAbsorption." + item for item in solution_imports[name]) + "\n"
    (OUT / (name + "Solution.lean")).write_text(solution, encoding="utf-8", newline="\n")
    config = {"challenge_module": "Palomar." + name + "Challenge", "solution_module": "Palomar." + name + "Solution",
              "theorem_names": names, "definition_names": [],
              "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "enable_nanoda": True}
    (OUT / (name + ".comparator.json")).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(name, len(challenge.splitlines()), len(challenge.encode()), "bytes", len(names), "theorems")
(ROOT / "provenance/palomar-extractions.json").write_text(json.dumps(spans, indent=2) + "\n", encoding="utf-8", newline="\n")
