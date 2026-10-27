module

public import RefinedAbsorption.Faithful2024.Section1
public import RefinedAbsorption.Faithful2024.Theorem37
public import RefinedAbsorption.Faithful2024.Section2
public import RefinedAbsorption.Faithful2024.Section6
public import RefinedAbsorption.FaithfulSurvey2025.Embedding

/-! Axiom check for the faithful endpoints (arXiv:2402.17855v1 and arXiv:2510.19978v1). -/

open RefinedAbsorption.Faithful2024 RefinedAbsorption.FaithfulSurvey2025

-- arXiv:2402.17855v1 (Delcourt–Postle), Theorems 1.7 and 1.11 (simple, host `G`)
#print axioms theorem_1_7
#print axioms theorem_1_11
-- arXiv:2402.17855v1, Theorems 3.7 and 3.8 (multigraph input, prescribed `Y`, flatness)
#print axioms theorem_3_8_conclusion
#print axioms theorem_3_8
#print axioms theorem_3_7_for_all
#print axioms theorem_3_7
#print axioms theorem_3_8_conclusion_via_3_7
-- arXiv:2402.17855v1, Lemma 6.4
#print axioms lemma_6_4
-- arXiv:2510.19978v1 (survey), Definition 3.7 / Lemma 3.8
#print axioms isGlobalEmbedding_iff
#print axioms IsGlobalEmbedding.injective_piece
#print axioms IsGlobalEmbedding.newEdgesDistinct
#print axioms not_generalEmbeddingLemmaLiteral
#print axioms generalEmbedding_piecewise
