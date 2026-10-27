---
title: 'Formalizing refined absorption: proof interfaces and consequences'
author: 'Juan Pablo Traverso Gianini'
date: '27 October 2026'
---

**Research note — preprint 1.0, 27 October 2026.**

**Editorial draft.** The formal source is frozen; DOI reservation and the public release remain pending.

© 2026 Juan Pablo Traverso Gianini. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

## Abstract

We describe a Lean formalization of principal results from Delcourt and Postle's refined absorption paper and Postle's survey, concentrating on the interfaces between their arguments. Three case studies explain reserve matching, avoidance in compatible decompositions, and the deduction of compatible absorbers. We distinguish independence of an old ambient vertex set from independence of its edge support, and give a finite obstruction to the survey's global embedding conclusion, alongside the proved piecewise variant. A completion theorem then yields prescribed sparse intersections, finite exact-intersection embeddings and an initial intersection interval of polynomial order. Finally, proved external colouring and Nash–Williams inputs give polynomial excess bounds for partial parallel classes and triangle-decomposition schedules. These are verified derivations and interface clarifications; historical priority for each consequence is not claimed. The accompanying formalization and reproducibility companion identifies the declarations, source versions, dependency pins and build evidence.

**Keywords:** refined absorption; designs; formalization; Steiner systems; intersections; hypergraph edge colouring.

## 1. Sources and purpose

An absorption proof is often read at two scales. At the larger scale, a sparse reserve and an absorber convert an approximate decomposition into an exact one. At the smaller scale, successive arguments have to pass the right object to one another: a family with a local load bound, a packing avoiding a prescribed family, or an embedding with precisely the injectivity that its consumer needs. Formalization makes those smaller interfaces explicit.

The sources here are Delcourt and Postle's *Refined Absorption: A New Proof of the Existence Conjecture* [1] and Postle's survey [2]. We use arXiv:2402.17855v1 for the article and arXiv:2510.19978v1 for the survey's statement baseline. The latter has appeared in the ICM 2026 proceedings. Its published DOI identifies the work; the arXiv version specifies the text against which the development began. The relevant embedding definitions and lemma were also checked in the published edition.

The library contains the refined omni-absorber and refiner endpoints of [1, Theorems 1.7 and 1.11], its dense decomposition and compatibility results, and the survey's refined efficient omni-absorber theorem. Its design-existence endpoint covers every fixed index $\lambda\ge1$ for $q>r\ge2$, with a set of blocks without repetitions, at all sufficiently large admissible orders. These remain results of the cited authors. We refer to their principal theorems rather than reproduce the full absorption development.

The purpose of this note is narrower. Sections 3 and 4 explain places where a proof interface needs care, including a distinction between the survey's global embedding assertion and a piecewise assertion. Sections 5 and 6 develop a few consequences from the established interfaces. The completion argument is particularly useful: it turns compatibility with one packing into exact control of common blocks.

This is a research note about formalization and its mathematical consequences, rather than a claim to a new existence theory. Intersection questions for Steiner triple systems are classical; the work of Lindner and Rosa [10], together with its corrigendum [11], precedes the present derivations. We do not claim a complete intersection spectrum or historical priority for every general-parameter corollary. The value of the formal development is that the hypotheses, intermediate objects and final applications can be followed through one checked collection of proofs.

## 2. A minimal framework

All objects are finite. Fix integers $q>r\ge1$, except where a stronger lower bound on $r$ is stated. An $r$-graph is a set of $r$-element edges. Write $K_V^r$ for the complete $r$-graph on $V$. For an $r$-graph $G$ and an $(r-1)$-set $S$, let
$$
d_G(S)=|\{e\in G:S\subseteq e\}|.
$$
The minimum and maximum of these degrees are denoted by $\delta_{r-1}(G)$ and $\Delta_{r-1}(G)$. For ordinary graphs these are the usual vertex degrees.

A $K_q^r$-decomposition of $G$ is a family of $q$-sets whose $r$-subsets partition $G$. A packing covers each edge at most once. A partial Steiner system is a family of $q$-sets in which each $r$-set occurs at most once; a Steiner system covers every $r$-set exactly once. For a block family $P$, write
$$
H(P)=\bigcup_{B\in P}\binom Br.
\tag{2.1}
$$
Thus $H(P)$ is an $r$-graph, while $P$ is a family of $q$-sets. Keeping those two levels separate will matter in the sparsity assumption in Section 5.

The usual divisibility condition for a simple design of index $\lambda$ is
$$
\binom{q-i}{r-i}\ \bigm|\ \lambda\binom{n-i}{r-i}
\qquad(0\le i<r).
\tag{2.2}
$$
We call $n$ admissible when (2.2) holds with $\lambda=1$. For a general host $G$, divisibility requires $\binom{q-i}{r-i}$ to divide the number of edges of $G$ containing each $i$-set. Subtracting the edges of a decomposition preserves these conditions.

The dense decomposition input is [1, Theorem 6.1]. Its compatible form, [1, Theorem 6.3], says that, for fixed $q>r\ge1$, a sufficiently large divisible host of minimum $(r-1)$-degree at least $(1-\varepsilon)n$ can be decomposed compatibly with any prescribed packing $Q_1$: its output $Q_2$ satisfies
$$
|B_1\cap B_2|\le r
\qquad(B_1\in Q_1,\ B_2\in Q_2).
\tag{2.3}
$$
The positive constant $\varepsilon$ and the order threshold depend only on $q,r$. In particular, the prescribed packing need not be sparse. Equation (2.3) excludes a common block because $q>r$.

## 3. Three proof interfaces

### 3.1. Reserve matching and local tests

The reserve-matching statement is [1, Theorem 2.8], whose matching background is [3]. Fix $s\ge2$ and $0<\beta<1$, writing $s$ for the uniformity of its auxiliary multi-hypergraph; this parameter is called $r$ in that theorem. Edges have labels, so different copies may have the same endpoints. The main part $G_1$ has degrees at most $D$ and degrees at least $D(1-D^{-\beta})$ on a designated set $A$. A second part $G_2$ supplies many options through each point of $A$, with exactly one such point per edge. Its other vertices have degree at most $D$, and the two vertex sets meet exactly in $A$. Codegrees are bounded by $D^{1-\beta}$.

The conclusion is a matching covering $A$. Near-regularity is required on $A$ in the main part; it is not an assumption on every vertex of the entire multi-hypergraph. The formal endpoint retains the labelled copies and the full reserve contract.

Here is the passage from the nibble to the reserve. Keep
$$
t=\lceil D^{1-\alpha}\rceil
$$
reserve options at each root $a\in A$, where $\alpha>0$ will be chosen below. For a reserve vertex $b\notin A$, let $w_b(a)$ count the retained options through both $a$ and $b$. The degree and codegree bounds give
$$
\sum_{a\in A}w_b(a)\le D,
\qquad
0\le w_b(a)\le\lfloor D^{1-\beta}\rfloor.
\tag{3.1}
$$
If $U\subseteq A$ is left uncovered by the nibble, the load still visible at $b$ is $\sum_{a\in U}w_b(a)$. A bound on $|U|$ alone would not control that sum: uncovered roots could be concentrated on the options using one vertex.

Use instead the level sets
$$
T_{b,j}=\{a\in A:w_b(a)\ge j\}.
$$
The nibble is applied with local tests drawn from these sets. Their sizes and the number through an individual vertex have polynomial bounds in $D$. No bound on the total number of tests, or on the total number of edges of the ambient multi-hypergraph, is inserted into this interface. Small level sets are handled by their size; the nibble controls the larger ones.

The local nibble supplies a constant $c>0$. Put $D_0=\lfloor D\rfloor$. The resulting bounds, in the convenient common form
$$
|U\cap T_{b,j}|
\le D_0^{-c}|T_{b,j}|+D_0^{\beta/2},
$$
can be summed over the integer levels. Indeed, counting each root once for every level below its weight gives
$$
\begin{aligned}
\sum_{a\in U}w_b(a)
&=\sum_{j=1}^{\lfloor D^{1-\beta}\rfloor}|U\cap T_{b,j}|\\
&\le D_0^{-c}D+
 \lfloor D^{1-\beta}\rfloor D_0^{\beta/2}.
\end{aligned}
\tag{3.2}
$$
This is the load estimate needed by the reserve argument. It explains why a local test-family interface is useful even when a global leftover estimate is already available.

For completeness, the numerical choices have a simple purpose. Set
$$
c'=\min\{c,\beta/2\},\qquad
\alpha=c'/8,\qquad p=D^\alpha/t.
\tag{3.3}
$$
Select reserve options independently with probability $p$. The bad events are that a root gets no option, or that two intersecting options are both selected. Their probabilities are bounded by $e^{-D^\alpha}$ and $p^2$, respectively. Equation (3.2) bounds the relevant reserve degrees by $O(D^{1-c'})$, and hence bounds the local dependencies. For the collision events the resulting product is of order $D^{3\alpha-c'}$, which tends to zero by (3.3); the exponential term also beats the polynomial dependency bound. The local lemma therefore supplies a matching covering the uncovered roots.

Its union with the nibble matching is still a matching. Reserve vertices outside $A$ do not belong to the main vertex set, and its roots in $U$ were uncovered. This last observation is the reason for retaining the exact vertex-set intersection in the interface. Floors, ceilings and eventual inequalities are checked in the formal proof; they do not alter this division of the argument.

### 3.2. Avoidance must survive absorption

For [1, Theorem 6.3], fix a packing $Q_1$ and let $\mathcal D$ be the family of dangerous $q$-sets: those meeting a block of $Q_1$ in at least $r+1$ vertices. The formal counting lemma gives, through each fixed $r$-edge $e$,
$$
|\{Q\in\mathcal D:e\subseteq Q\}|
\le 2^r q\,n^{q-r-1}.
\tag{3.4}
$$
This is one power smaller than the order $n^{q-r}$ of the available cliques through an edge.

To see the saving, let $P\in Q_1$ witness that $Q$ is dangerous and put $A=e\cap P$. Choose $B\subseteq(Q\cap P)\setminus e$ so that $|A\cup B|=r$, then choose one more point $y\in(Q\cap P)\setminus(A\cup B)$. The $r$-set $A\cup B$ determines at most one block $P$ because $Q_1$ is a packing. There are at most $2^r$ choices for $A$, at most $n^{r-|A|}$ choices for $B$, and at most $q$ choices for $y$ once $P$ is determined. The remaining points of $Q$ contribute at most $n^{q-2r+|A|-1}$. If the forced set is too large, there is no such $Q$. Otherwise the exponents sum to $q-r-1$, giving (3.4).

The final paragraph of the relevant discussion in [1, Section 6.3] prints the looser order $n^{q-r+1}$. A stronger upper bound does not contradict that upper bound. The issue for the proof is that the looser estimate does not supply the saving used when deleting dangerous cliques. Equation (3.4) supplies it.

There are two places to impose avoidance. First, the catalogue of blocks available to the omni-absorber must be safe against $Q_1$. Second, the nibble and its reserve completion must use safe blocks. Restricting only the final approximate packing would leave the absorber's selected decomposition uncontrolled.

After the safe absorber is chosen, remove it and the reserve from the working host. Regularity boosting supplies the clique family for the main covering step. The deletion budget in (3.4) is small enough to retain the required supply, and the safe nibble leaves a divisible remainder in the reserve. The absorber then handles that remainder using its already safe catalogue. Both block families in the final union satisfy (2.3), so the union does too. The library treats $r=1$ separately; the preceding nibble discussion concerns $r\ge2$.

### 3.3. Compatible absorbers from compatible decompositions

The deduction of [1, Theorem 6.2] can be expressed without another absorption construction. Let $L$ be the given divisible $r$-graph on its old vertex set. Choose an admissible set $U$ containing every old vertex, then a much larger admissible set $W\supseteq U$. Put
$$
A_0=K_W^r\setminus K_U^r.
\tag{3.5}
$$
Both complete hosts are divisible, so $A_0$ is divisible. Taking $W$ sufficiently large relative to $U$ makes $A_0$, and also $A_0\cup L$, dense enough for the two decomposition inputs.

Apply [1, Theorem 6.1] to obtain a decomposition $Q_1$ of $A_0$. It is a packing in $A_0\cup L$. Apply [1, Theorem 6.3] to that larger host with prescribed packing $Q_1$, obtaining a decomposition $Q_2$ satisfying (2.3). Thus $A_0$ and $A_0\cup L$ have compatible decompositions.

Every edge of $A_0$ uses a vertex outside $U$. Consequently the entire old vertex set is independent in $A_0$. Relabelling the added vertices while fixing the old ones gives the desired absorber. The construction separates three obligations: divisibility by subtraction, density by enlargement, and compatibility by the prescribed-packing theorem. It also exposes the ambient-vertex condition discussed next.

## 4. Two fidelity distinctions

### 4.1. Old vertices and edge support

An edge-set representation remembers the vertices occurring in edges. A hypergraph with an explicit ambient vertex set can also have isolated vertices. These conventions are interchangeable for many edge-counting statements, but the phrase “the old vertices are independent” requires the old set to be identified.

The retained absorber predicate uses the support of $L$. The added interface for the article's Theorem 6.2 also states that no absorber edge is wholly contained in the full old ambient set, including isolated labels. Construction (3.5) proves this directly because all old vertices were included in $U$. Mixed edges containing old and new vertices are permitted.

The old endpoint is retained. The added clause records information already supplied by the same construction; it is not presented as a new absorber existence theorem. This is a useful distinction between strengthening the public interface and changing the underlying proof.

### 4.2. Global and piecewise embeddings

The survey's Definition 3.7 asks for one injective map on the union of a system of supergraphs, fixing the old host vertices. Its Lemma 3.8 draws a conclusion of that kind from local embedding counts and a sparsity assumption. The formalization separates global injectivity, injectivity on each individual piece, and distinctness of the images of new edges.

There is a finite obstruction to the global conclusion. Take an even $n$ and let $J$ be a perfect matching spanning $K_n$. For each matching edge $H$, add a private new vertex to make a triangle $W_H$. With the survey's parameters
$$
r=2,\qquad C=3,\qquad \gamma=1/2,
\tag{4.1}
$$
each piece has $n-2\ge n/2$ rooted embeddings for $n\ge4$. The other matching edges do not obstruct these embeddings: the two new edges of the triangle meet the endpoints of $H$. The refinement and bounded-size conditions hold with $C=3$. Moreover $\Delta(J)=1$, so the sparsity inequality $\Delta(J)\le n/C'$ holds for any proposed constant $C'$ once $n$ is sufficiently large.

Yet a global injection fixing all $n$ old vertices has no image available for even one private new vertex. The pieces cover every old vertex, so this obstruction also applies if the global domain is defined using only old vertices occurring in the indexed pieces. It does not depend on a convention about unused old vertices.

The survey refers to [4, Appendix B] for a proof. That appendix is available and includes a proof; it also writes a global injection in its definition. The issue here is the conclusion, rather than a missing reference. Its extension argument controls local loads and collisions of new edges. Those controls should be distinguished from injectivity on all vertices of the union.

The library proves a piecewise variant with distinct images of new edges. A new vertex of one piece may then coincide with a vertex belonging to another piece, provided the individual embedding and edge conditions are satisfied. Global injectivity would forbid those coincidences. The proved variant and the formal negation of the global assertion have separate declarations. Neither is described as a proof of the other.

## 5. Completion and exact intersections

The compatible decomposition interface gives a short completion argument. We state it with its full sparsity condition because that condition is easy to misread.

#### Theorem 5.1

For fixed $q>r\ge1$ there are $\varepsilon>0$ and $n_0$ such that the following holds for every admissible $n\ge n_0$. Let $P,F$ be partial Steiner systems on the same $n$ points. If
$$
\Delta_{r-1}(H(P))\le\varepsilon n,
\tag{5.1}
$$
there is a Steiner system $\mathcal S$ with
$$
P\subseteq\mathcal S,\qquad
\mathcal S\cap F=P\cap F.
\tag{5.2}
$$
Furthermore, if $B\in F$ has no $r$-edge in $H(P)$, then
$$
|B\cap B'|\le r
\qquad(B'\in\mathcal S\setminus P).
\tag{5.3}
$$
No sparsity assumption is made on $F$.

*Proof.* Remove $H(P)$ from the complete $r$-graph and call the residual host $G$. The family $P$ decomposes the removed edges. Divisibility therefore passes from $K_n^r$ to $G$. Condition (5.1) removes at most $\varepsilon n$ extensions of each $(r-1)$-set; after choosing $\varepsilon$ small enough and $n_0$ large enough, $G$ meets the minimum-degree hypothesis of the article's Theorem 6.3.

Let $F_0$ consist of the blocks of $F$ all of whose $r$-subsets lie in $G$. It is a packing in $G$. Apply [1, Theorem 6.3] with prescribed packing $F_0$ and write $Q$ for the resulting decomposition of $G$. No block of $Q$ belongs to $F_0$: a common block would have intersection size $q>r$ with itself. A block of $F\setminus F_0$ cannot belong to $Q$ either, because one of its $r$-edges was removed.

It follows that $Q\cap F=\varnothing$. The family $\mathcal S=P\cup Q$ decomposes the complete $r$-graph and satisfies (5.2). If $B$ obeys the additional condition in the theorem, then $B\in F_0$. The crossing conclusion from [1, Theorem 6.3] gives (5.3) for the new blocks. $\square$

The sparsity in (5.1) measures the covered $r$-edges through an $(r-1)$-set. It is not stated as a point-degree bound on the family of $q$-blocks. The restriction preceding (5.3) also matters: the theorem makes no such crossing assertion for a forbidden block using an edge already covered by $P$.

#### Corollary 5.2

For fixed $q>r\ge1$, the following statements hold.

(i) Every sufficiently large Steiner system $\mathcal S_1$ and every subfamily $P\subseteq\mathcal S_1$ satisfying (5.1), for a suitable fixed $\varepsilon>0$, admit a Steiner system $\mathcal S_2$ with
$$
\mathcal S_1\cap\mathcal S_2=P.
\tag{5.4}
$$
Blocks of $\mathcal S_1\setminus P$ and $\mathcal S_2\setminus P$ have intersection size at most $r$.

(ii) Every finite partial Steiner system occurs, after an injection of its vertex set, as the exact common block family of two Steiner systems at every sufficiently large admissible order.

*Proof.* For (i), use $F=\mathcal S_1$ in Theorem 5.1. The existence of $\mathcal S_1$ supplies admissibility. A block of $\mathcal S_1\setminus P$ has no $r$-edge in $H(P)$, since otherwise that edge would lie in two blocks of $\mathcal S_1$. Thus the last assertion follows from (5.3).

For (ii), first use the ordinary sparse completion theorem to extend a sparse partial system to $\mathcal S_1$, then apply (i). The sparsity constants can be reduced so that both steps apply. For a fixed finite system on a vertex set of size $u$, embed that vertex set into a larger set of size $N$. Its covered $r$-graph has maximum $(r-1)$-degree at most $u$: each extension chooses one point of the embedded set. Hence its degree is at most $\varepsilon N$ for every sufficiently large $N$. Choose $N$ above both completion thresholds and impose admissibility. The construction chooses an injection and the two systems together. $\square$

Taking $P=\varnothing$ in Theorem 5.1 supplies a Steiner system with no common block with any prescribed partial system, and with the crossing bound (5.3). In particular every sufficiently large Steiner system has a disjoint mate. “Disjoint” concerns their block families; both systems still cover the same complete $r$-graph.

#### Proposition 5.3

For fixed $q>r\ge1$ there are $c>0$ and $n_0$ such that, for every admissible $n\ge n_0$ and every integer $0\le k\le c n^r$, two Steiner systems on $n$ points have exactly $k$ common blocks.

*Proof.* Choose the sparse-completion constant with $0<\varepsilon\le1$, and reserve a set of $u=\lfloor\varepsilon n\rfloor$ points. A greedy packing on that set can have $k$ blocks whenever
$$
2\binom qr^2 k\le\binom ur.
\tag{5.5}
$$
To see the available slack, each selected block rules out at most $\binom qr\binom{u-r}{q-r}$ candidate blocks containing one of its $r$-sets. Counting all candidates by $\binom uq$ gives (5.5) as a sufficient condition throughout the greedy construction.

The covered $r$-graph of this partial system has maximum $(r-1)$-degree at most $u$, so the exact-intersection construction in Corollary 5.2 applies. For all sufficiently large $n$,
$$
\binom{\lfloor\varepsilon n\rfloor}{r}
\ge\frac{(\varepsilon n/2)^r}{r!}.
$$
Thus one may take
$$
c=\frac{(\varepsilon/2)^r}{2r!\binom qr^2},
\tag{5.6}
$$
after enlarging the order threshold. The resulting two systems have precisely the chosen $k$ blocks in common. $\square$

The proposition chooses both systems. It does not give the full spectrum, or prescribe $k$ common blocks with every fixed first system. Its role here is to show how exact completion and a small-support packing yield an interval of the same polynomial order as the total number of blocks.

## 6. Polynomial bounds for classes and schedules

### 6.1. The colouring input

A partial parallel class is a family of pairwise vertex-disjoint blocks. Partitioning a block family into such classes is proper edge colouring of the hypergraph whose edges are the blocks.

The quantitative input used here is proved in the pinned Pippenger–Spencer development via the pseudorandom matching theorem of Ehard, Glock and Joos [6, Theorem 1.2]. The classical context is [5]; we do not identify the following exact contract with the printed 1989 theorem.

For fixed $k\ge2$ and $0<\delta<1$, there are $\gamma_0>0$ and $D_*$ such that a $k$-uniform hypergraph with maximum degree at most $D\ge D_*$, codegrees at most $D^{1-\delta}$, and
$$
|E|\le\exp(D^{\gamma_0})
\tag{6.1}
$$
has a proper edge colouring using at most $D+D^{1-\gamma_0}$ colours. There is no minimum-degree assumption. The edge-count cap (6.1) is part of the input and must be checked.

### 6.2. Steiner systems

#### Theorem 6.2

Fix $q>r\ge2$. There are $0<\gamma<1$ and $n_0$ such that every Steiner system on $n\ge n_0$ points has a partition into partial parallel classes whose number is at most
$$
R+R^{1-\gamma},\qquad
R=\frac{\binom{n-1}{r-1}}{\binom{q-1}{r-1}}.
\tag{6.2}
$$
Such a system exists at every sufficiently large admissible order. Every partition into partial parallel classes requires at least $R$ classes.

*Proof.* In the $q$-uniform block hypergraph, counting the $r$-sets through a point and through a pair gives
$$
d(v)=R,\qquad
d(u,v)=R\frac{q-1}{n-1}\quad(u\ne v),\qquad
q|\mathcal S|=nR.
\tag{6.3}
$$
In particular $R$ is an integer. Use the colouring input with $D=R$ and $\delta=1/(2(r-1))$. The binomial formula gives $R\le(n-1)^{r-1}$, hence $R^\delta\le\sqrt{n-1}$. For large $n$ we also have $q-1\le\sqrt{n-1}$. The codegree identity in (6.3) now gives $d(u,v)\le R^{1-\delta}$.

For large $n$, every pair belongs to a block, so its codegree is at least one. Equation (6.3) gives $n-1\le R(q-1)$; since $R\ge1$, this implies $n\le qR$. Together with the block-count identity this gives, in particular, the polynomial bound $|\mathcal S|\le qR^2$. As $R$ tends to infinity, that bound implies (6.1) for the exponent $\gamma_0$ actually supplied by the colouring input. Apply that input first, then put $\gamma=\min\{\gamma_0,1/2\}$ to obtain (6.2). Blocks in one colour class are vertex-disjoint. The $R$ blocks through a fixed point need distinct colours, proving the lower bound. Finally combine this statement with the established existence theorem for Steiner systems. $\square$

The polynomial error in (6.2) counts excess classes. It gives no bound on the number of uncovered vertices in every individual class, and it does not assert a resolution into spanning classes. The two formal endpoints separate colouring every existing system from existence at admissible orders.

### 6.3. Nash–Williams schedules

The graph decomposition input is Delcourt and Postle's large-order Nash–Williams theorem [7]. We reuse its proved formal endpoint via the constructions documented in [8,9]. No argument from those papers is repeated here.

#### Theorem 6.3

There are $0<\gamma<1$ and $n_0$ such that every triangle-divisible graph $G$ on $n\ge n_0$ vertices with
$$
3n\le4\delta(G)
\tag{6.4}
$$
has a triangle decomposition whose number of rounds is at most
$$
D+D^{1-\gamma},\qquad D=\Delta(G)/2,
\tag{6.5}
$$
with vertex-disjoint triangles in each round. Every such schedule needs at least $D$ rounds.

*Proof.* Triangle divisibility means that every degree is even and $3$ divides the number of edges. The proved Nash–Williams input supplies a triangle decomposition $T$ at the exact threshold (6.4). Regard its triangles as a $3$-uniform hypergraph. At a vertex $v$ its degree is $d_G(v)/2$, and a pair has codegree at most one because an edge of $G$ belongs to just one triangle. Its maximum degree is therefore $D$.

There is no need for $G$ to be nearly regular: the colouring input asks only for an upper degree bound. Counting vertex–triangle incidences gives $3|T|\le nD$, while (6.4) gives $D\ge3n/8$. In particular $|T|\le3D^2$. With $\delta=1/2$, the codegree and edge-count hypotheses of Section 6.1 hold for sufficiently large $n$. Colour the triangle hypergraph, and reduce the output exponent to $\gamma=\min\{\gamma_0,1/2\}$ as before. Its colour classes give the required rounds. At a maximum-degree vertex, the $D$ incident triangles must occur in different rounds, proving the lower bound. $\square$

Some colour labels may be unused; only the asserted upper bound on rounds is needed. The rounds are families of vertex-disjoint triangles, rather than necessarily spanning triangle factors. The constants and thresholds in both applications are existential and are not claimed to be optimized.

## 7. Formal scope and reproducibility

The proofs are implemented in Lean 4 [12] using Mathlib [13]. The formal freeze uses Lean `4.35.0-rc3` and fixed dependency revisions. Its clean project Lake campaign compiled 316 local sources: 300 library modules, ten check modules and six standalone comparison interfaces. The 360 endpoint queries use only `propext`, `Classical.choice` and `Quot.sound`, or no axioms. Deliberate placeholders in the comparison Challenges are statement interfaces; their Solutions import the actual proved declarations.

The aggregate root imports the full local proof library. The earlier conditional colouring and scheduling consumers are retained, while the final assembly supplies both external contracts from pinned proofs. The companion records the exact declarations and distinguishes this local evidence from Palomar's separate comparison and kernel checks.

The formalized scope is selective. It includes the full fixed-index existence endpoint described in Section 1, but not every application in the article or survey; general high-girth assertions are outside the established scope. The piecewise embedding result is a variant, and the literal global assertion has a separate formal counterexample. These qualifications are part of the mathematical account.

The development was produced under the author's direction with Aristotle and Codex. Aristotle contributed proof development and formalization. Codex contributed migration, assembly, interface work, exposition and the internal audit. The author is responsible for the mathematical and editorial claims. The internal agent review is not independent human peer review.

## References

[1] M. Delcourt and L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture*, arXiv:2402.17855v1 (2024). <https://doi.org/10.48550/arXiv.2402.17855>.

[2] L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture and Its Applications to Extremal and Probabilistic Design Theory*, Proceedings of the International Congress of Mathematicians 2026, Volume 6, 212–231. <https://doi.org/10.1137/25M1805977>. Statement baseline: arXiv:2510.19978v1 (2025), <https://doi.org/10.48550/arXiv.2510.19978>.

[3] M. Delcourt and L. Postle, *Finding an Almost Perfect Matching in a Hypergraph Avoiding Forbidden Submatchings*, arXiv:2204.08981. <https://doi.org/10.48550/arXiv.2204.08981>.

[4] M. Delcourt, C. Henderson, T. Lesgourgues and L. Postle, *Erdős meets Nash-Williams*, arXiv:2507.23624v1 (2025), Appendix B. <https://doi.org/10.48550/arXiv.2507.23624>.

[5] N. Pippenger and J. Spencer, *Asymptotic behavior of the chromatic index for hypergraphs*, Journal of Combinatorial Theory, Series A 51 (1989), 24–42. <https://doi.org/10.1016/0097-3165(89)90074-5>.

[6] S. Ehard, S. Glock and F. Joos, *Pseudorandom hypergraph matchings*, Combinatorics, Probability and Computing 29(6) (2020), 868–885. <https://doi.org/10.1017/S0963548320000280>.

[7] M. Delcourt and L. Postle, *A Proof of Nash-Williams' Conjecture*, arXiv:2606.11178 (2026). <https://doi.org/10.48550/arXiv.2606.11178>.

[8] J. P. Traverso Gianini, *Triangle decompositions I: Formalizing the Nash–Williams theorem in Lean*, preprint 1.0 (2026). <https://doi.org/10.5281/zenodo.23428173>.

[9] J. P. Traverso Gianini, *Triangle decompositions II: Robust absorption for typed triangles*, preprint 1.0 (2026). <https://doi.org/10.5281/zenodo.23502224>.

[10] C. C. Lindner and A. Rosa, *Steiner triple systems having a prescribed number of triples in common*, Canadian Journal of Mathematics 27(5) (1975), 1166–1175. <https://doi.org/10.4153/CJM-1975-122-4>.

[11] C. C. Lindner and A. Rosa, *Steiner triple systems having a prescribed number of triples in common (corrigendum)*, Canadian Journal of Mathematics 30(4) (1978), 896. <https://doi.org/10.4153/CJM-1978-077-9>.

[12] L. de Moura and S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, Automated Deduction — CADE 28 (2021), 625–635. <https://doi.org/10.1007/978-3-030-79876-5_37>.

[13] The mathlib Community, *The Lean Mathematical Library*, Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (2020), 367–381. <https://doi.org/10.1145/3372885.3373824>.
