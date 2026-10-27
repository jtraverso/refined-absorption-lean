# Mathematical review notes before manuscript drafting

These notes guide the later semantic audit. Build status is recorded separately; none of these observations is a substitute for the clean Lake certificate.

## Preserved substance and additive interfaces

The original 300 returned sources retain their declarations. The migration's comparison finds no changes to the 821 non-proof declaration spans, including structures, after ignoring comments and whitespace. The subsequent module relocation preserves the 301 migrated source files exactly after the documented import-prefix substitution. The original declaration namespaces remain in use.

The three quantitative consumers in Assembly discharge their external hypotheses with proved pinned endpoints. Their conditional predecessors remain available. The additional Faithful2024.theorem_6_2_ambient exposes independence of all old vertices, including isolated labels; Pending.theorem_6_2 remains unchanged. The new proof follows the same admissible-host construction and adds its ambient-independence check.

The last returned round contains the full arbitrary-index existence endpoint, RefinedAbsorption.existenceConjecture_proved. Its type is ExistenceConjecture for q > r ≥ 2 and λ ≥ 1, with a finite set of blocks. It was included in the migration axiom checks. Restricting the reported established existence scope to λ = 1 would omit this result. General high-girth applications remain outside the proved scope.

## Reserve matching: original article, Theorem 2.8

The endpoint permits labelled parallel edge copies and near-regularity only on A. It must not be replaced by a near-regularity assumption on every vertex. The local nibble controls both the size of each test set and the number of test sets through each vertex; it does not impose a global bound on the number of tests or on the total number of hypergraph edges.

For each reserve root a, retain t options. For b outside A let w_b(a) count options using b. Then w_b(a) is bounded by the codegree and the sum over a is at most D. Apply the nibble to the level sets of these integer weights. The layer-cake identity converts leftover counts in level sets into the load bound

    ΔB ≤ D₀^(−c) D + floor(D^(1−β)) D₀^(β/2),  D₀ = floor(D).

The local lemma closes the uncovered roots with reserve options. The final union is a matching because the two ambient vertex sets meet exactly in A and only uncovered roots receive reserve edges. The formal parameters choose α = min(c, β/2)/8. Floors, ceilings and eventual inequalities are retained in the code; the note should explain their purpose without listing the entire numerical checklist.

## Compatible decompositions: original article, Theorems 6.3 and 6.2

For a fixed r-edge e, dangerous q-sets meet a packing block in at least r+1 points. Choose A = e ∩ P, extend it inside the dangerous intersection to an r-set A ∪ B, and choose one more point y of P outside e ∪ B. The r-set identifies at most one packing block. Counting A, B, y and the remaining vertices gives the formal bound 2^r q n^(q−r−1). Cases in which the forced set exceeds q give no q-sets. This is an explicit saving against order n^(q−r), as required by deletion after regularity boosting.

Both stages need avoidance: the private absorber family and the nibble/reserve covering. Avoiding dangerous cliques only in the final packing does not control the absorber decomposition. The final absorption identity joins the packing and the selected absorber decomposition, both already safe. The r=1 case is handled separately in the library.

For 6.2, choose admissible orders |U| and |W|, with W much larger and U containing every old vertex of L. Put A₀ = K_W^r minus K_U^r. Divisibility follows by subtraction, and density follows because U is small relative to W. Apply 6.1 to A₀ and 6.3 to A₀ ∪ L with the first decomposition as the prescribed packing. Every edge of A₀ uses a vertex outside U, which proves the ambient-independence clause before relabelling.

## Embedding fidelity: survey, Definition 3.7 and Lemma 3.8

Use source-qualified theorem numbers. The survey's Lemma 3.8 is unrelated to the original article's Theorem 3.8. The formalization distinguishes global injectivity, injectivity on each piece and distinctness of new edges.

The counterexample takes r=2, C=3, γ=1/2, a perfect matching spanning an even n-vertex complete graph, and a privately extended triangle for each matching edge. Each piece has n−2 ≥ n/2 rooted embeddings when n ≥ 4; the matching has degree 1, so any prescribed sparsity constant is met by taking n large. All old vertices are fixed, leaving no host vertex for a new vertex under a global injection. The cited Appendix B proof is available; the issue is the global conclusion, not a missing reference. The piecewise theorem is a proved variant and must be identified as such.

The coded global domain uses old vertices occurring in the indexed pieces. In the counterexample those pieces cover every vertex of J, so this domain convention agrees with the full old vertex set on the witness. The refutation does not depend on how unused or isolated old vertices are added to a general system's domain. Avoid claiming a generic definitional identity across every ambient-vertex convention merely from this counterexample.

## Completion and intersections

Write H(P) for the covered r-edges of a partial Steiner system. Sparsity is a bound on Δ_(r−1)(H(P)), not on the point degrees of the block family. The forbidden partial system F is arbitrary and need not be sparse.

Remove H(P) from the complete r-graph. Divisibility survives because P decomposes H(P); density survives by sparsity. Filter F to the blocks wholly contained in the residual graph and apply 6.3. A forbidden block using a removed edge cannot occur in a residual decomposition; a wholly residual forbidden block cannot coincide with an output block because q > r and the cross-intersection bound is r. Adding P back gives S ∩ F = P ∩ F. The additional cross-intersection guarantee applies only to forbidden blocks whose r-edges avoid H(P).

Prescribed intersections take F to be a fixed Steiner system and P a sparse subfamily. Finite embedding yields every sufficiently large admissible order, rather than one order. The polynomial spectrum chooses both systems and gives an initial interval 0 ≤ k ≤ c n^r; it is not a complete spectrum or a statement about every fixed first system. The greedy sufficient condition is 2 binom(q,r)^2 k ≤ binom(u,r), with P supported on u points proportional to n. The mate statements mean no common blocks. They do not mean edge-disjoint decompositions or classical Steiner orthogonality.

## Polynomial colouring and graph schedules

For a Steiner system, the q-uniform block hypergraph has degree R = binom(n−1,r−1)/binom(q−1,r−1), codegree R(q−1)/(n−1), and q|S|=nR. The quantitative input applies to maximum degree, polynomially small codegrees and an exponential edge-count cap. All three must be checked. Use δ=1/(2(r−1)); polynomial block counts satisfy the cap for the exponent γ₀ returned by the input. Only after that application weaken the output exponent to min(γ₀,1/2).

For a triangle decomposition of G, the triangle hypergraph has degree d_G(v)/2, codegree at most 1 and maximum degree D=Δ(G)/2. Its degrees need not be nearly equal. The exact Nash–Williams threshold gives D ≥ 3n/8; the bound |T| ≤ 3D² verifies the exponential cap for large D. Every round has vertex-disjoint triangles, and any schedule needs at least D rounds.

The additive polynomial error concerns the number of partial parallel classes or rounds. It gives neither perfect parallel classes nor an individual bound on the uncovered vertices in every round. The main note should state an upper bound on the number of rounds and explain the lower bound separately, without assuming every colour label is used. Thresholds and exponents are existential and are not claimed to be optimized.

The Steiner endpoints write the binomial quotient in `Nat` before casting it to the reals. The regularity counting identity proves the required divisibility, so this is exactly the usual point degree R, not an additional floor approximation. The companion should explain that representation detail. For finite exact-intersection embedding, the endpoint chooses an injection together with the two systems; do not strengthen it to a statement about every previously prescribed injection.

## Attribution and audit boundary

Attribute the source theorems to their original authors, including the existence theorem and Nash–Williams theorem. The polynomial colouring endpoint is a consequence of Ehard–Glock–Joos in the pinned Pippenger–Spencer development; do not attribute its exact quantitative contract directly to the 1989 paper. Classical triple-system intersection results and their corrigendum precede the note. The note claims a verified derivation and useful proof interfaces, without priority claims for every corollary.

The internal audit is performed by Codex under the author's direction. It is not independent human peer review. Local compilation, endpoint axiom queries, public-root coverage, text preservation, Comparator, Palomar preflight and registry review are distinct kinds of evidence and must not be conflated.
