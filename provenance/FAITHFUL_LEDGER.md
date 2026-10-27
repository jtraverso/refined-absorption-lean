# Ampliación fiel (estrictamente aditiva)

Fuentes, con sus numeraciones por separado:

1. **[DP24]** M. Delcourt y L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture*,
   arXiv:2402.17855v1. Namespace Lean: `RefinedAbsorption.Faithful2024`.
2. **[P25]** L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture and its
   Applications to Extremal and Probabilistic Design Theory* (survey), arXiv:2510.19978v1. Namespace
   Lean: `RefinedAbsorption.FaithfulSurvey2025`.

Leí directamente los enunciados y las definiciones en los PDF de ambos textos. **No pude consultar**
la referencia [10] del survey (la prueba del Lema 3.8 del survey) ni la referencia [5] de [DP24] (la
prueba del Teorema 2.8). Lo que digo abajo sobre esas pruebas se apoya solo en el texto impreso de
[DP24] y [P25].

## Integridad de lo existente

* No modifiqué ningún archivo existente. `checks/faithful_integrity/before_sha256.txt` registra los
  270 archivos versionados en el commit base `a2dca1e`, y `after_sha256.txt` los mismos archivos al
  terminar. Ambos ficheros son idénticos (`diff` vacío). `git diff --name-status a2dca1e HEAD` solo
  muestra archivos añadidos (`A`).
* Siguen intactas todas las interfaces anteriores (`Original2024`, `Final`, `GeneralEmbedding`, …).
* `lake build` (objetivo por defecto, que incluye todos los módulos `RequestProject.*`, antiguos y
  nuevos) termina sin errores.
* Los archivos nuevos no contienen `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` ni
  `implemented_by`.

## Archivos nuevos

| Archivo | Contenido |
|---|---|
| `RequestProject/Faithful2024/Defs.lean` | Definiciones fieles (Def. 1.5, 1.6, 1.8, 1.9, 1.10, 3.1, 3.2, 3.5, 3.6) y enunciados `Theorem_1_7`, `Theorem_1_11`, `Theorem_3_7_for`, `Theorem_3_7`, `Theorem_3_8_conclusion`, `Theorem_3_8_for` |
| `RequestProject/Faithful2024/Transport.lean` | Transporte de las definiciones fieles a lo largo de inyecciones |
| `RequestProject/Faithful2024/Section1.lean` | `theorem_1_7`, `theorem_1_11` |
| `RequestProject/Faithful2024/FlatSparsify.lean`, `FlatLabelled.lean`, `Theorem38Two.lean`, `Theorem38One.lean` | Teorema 3.8 (`r ≥ 2` y `r = 1`) |
| `RequestProject/Faithful2024/MultiGadget.lean`, `Theorem37Aux.lean`, `Theorem37.lean` | Teorema 3.7 |
| `RequestProject/Faithful2024/Section2.lean` | Def. 2.6, 2.7 y enunciado del Teorema 2.8 |
| `RequestProject/Faithful2024/Section6.lean` | Enunciados de los Teoremas 6.2 y 6.3; Lema 6.4 demostrado |
| `RequestProject/FaithfulSurvey2025/Embedding.lean` | Def. 3.7 y Lema 3.8 del survey: tres nociones de embedding, comparación y refutación de la lectura literal |
| `checks/FaithfulAxioms.lean`, `checks/FaithfulAxioms.out` | `#print axioms` de los endpoints y su salida |
| `checks/faithful_integrity/*` | Hashes de antes y después |

## Tabla de resultados

Categorías: **EFD** = enunciado fiel demostrado; **VD** = variante demostrada; **AP** = adaptación
pendiente; **A** = abierto (el enunciado está, la prueba no).

Todos los endpoints demostrados dependen únicamente de `propext`, `Classical.choice` y `Quot.sound`
(salida en `checks/FaithfulAxioms.out`).

| Fuente | Original | Declaración Lean | Diferencias de representación | Adaptadores | Compila | Estado |
|---|---|---|---|---|---|---|
| [DP24] | Def. 3.5 `M(q,r)` | `multBound` | — | — | sí | definición |
| [DP24] | Def. 1.5/3.1 (multi-omniabsorbedor), 1.6 | `IsMultiOmniAbsorberF`, `IsCRefinedMultiOmni` | multihipergrafo = copias etiquetadas `ends : E → Finset V`; incluye conjunto ambiente `U`, `|H ∩ X| ≤ 1` y familia de cliques (copias de `K_q^r` sin aristas repetidas) | — | sí | definición |
| [DP24] | Def. 1.8/3.2 (multi-refiner), 1.9, 1.10 | `IsMultiRefinerF`, `IsCRefinedMultiFamily`, `mrefDeg` | como arriba; `Δ(ℋ)` de la **familia** | — | sí | definición |
| [DP24] | Def. 3.6 (planitud) | `Original2024.IsFlatTo (r-1) Y` | exactamente `|e \ Y| ≤ r-1` para cada arista `e` | — | sí | definición |
| [DP24] | **Teorema 3.8** | `Theorem_3_8_conclusion`, **`theorem_3_8_conclusion`** | `X` multihipergrafo de multiplicidad `≤ M(q,r)` en `Fin n` (`v(X)=n`, vértices aislados incluidos), `n ≥ C`, `Y` prescrito con `|Y| ≥ n/3`, **sin** `Δ(X) ≤ n/C`. Salida: refiner `C`-refinado, su familia, `Δ(ℋ) ≤ C·max{Δ(X), n^{1-1/r} log n}` y `R` plano respecto de `Y`. Las copias de `X` se conservan mediante un reetiquetado inyectivo `g` con `ends'(g c) = ends c` | `isMultiRefinerF_of_residual`, `isCRefinedMultiFamily_of_residual` | sí | **EFD** |
| [DP24] | Teorema 3.8, forma inductiva («supongamos el Teorema 3.7 para `r' < r`») | `Theorem_3_8_for`, `theorem_3_8`; `theorem_3_8_conclusion_via_3_7` | la hipótesis es exactamente el Teorema 3.7 en uniformidades inferiores; queda descargada por `theorem_3_7` | — | sí | **EFD** |
| [DP24] | **Teorema 3.7** | `Theorem_3_7_for`, `Theorem_3_7`, **`theorem_3_7_for_all`**, **`theorem_3_7`** | mismas convenciones que en 3.8; salida: multi-omniabsorbedor `C`-refinado con `|H∩X| ≤ 1`, `Δ(A) ≤ C·Δ` y `A` plano respecto de `Y` | la prueba sigue §5.1: Teorema 3.8 + gadgets absorbentes multigrafo (`exists_multiGadget`) + colocación en `Y` (`multiCliqueEmbedding`) | sí | **EFD** |
| [DP24] | Teorema 1.7 | `Theorem_1_7`, **`theorem_1_7`** | `HGraph` con conjunto de vértices explícito (igualdad de conjuntos ambiente, no de soportes); anfitrión `G` con `δ(G) ≥ (1-ε)n`; `oneX` y `𝓗(e)` en el contrato | adaptador desde `Original2024.theorem_1_7_strong` | sí | **EFD** |
| [DP24] | Teorema 1.11 | `Theorem_1_11`, **`theorem_1_11`** | como 1.7; conclusión sobre `Δ(𝓗)` de la **familia** (`refDegree`) | adaptador desde `Original2024.theorem_1_11_strong` | sí | **EFD** |
| [DP24] | Def. 2.6, 2.7 | `IsAPerfectMatching`, `IsBipartiteHyp` | Def. 2.7 tal como está impresa (no exige `A ∩ B = ∅`) | — | sí | definición |
| [DP24] | **Teorema 2.8** (nibble con reservas) | `Theorem_2_8` | multihipergrafo `G = G₁ ⊔ G₂`, codegrados `≤ D^{1-β}`, todas las condiciones de grado de `G₁` y `G₂` | ninguno: los consumidores especializados del proyecto (`NibbleWithReserves*`, `localNibble`) **no** lo sustituyen | sí (solo el enunciado) | **A** |
| [DP24] | Teorema 6.2 | `Theorem_6_2` | absorbedor en `Fin m ⊕ Fin h`; `|V(Q₁) ∩ V(Q₂)| ≤ r` para **todos** los pares | — | sí (solo el enunciado) | **A** |
| [DP24] | Teorema 6.3 | `Theorem_6_3` | anfitrión en `Fin n`, `δ(G) ≥ (1-ε)n`, empaquetamiento `Q₁` dado | — | sí (solo el enunciado) | **A** (el artículo solo esboza la prueba) |
| [DP24] | **Lema 6.4** | `Lemma_6_4`, **`lemma_6_4`** | `V(L)` = todo el conjunto ambiente `Fin m` (lectura más fuerte); absorbedor en `Fin m ⊕ Fin h` | usa `absorberLibrary` (Teorema 1.4 del proyecto) | sí | **EFD** |
| [P25] | Def. 3.7 impresa (una sola `φ : V(⋃𝒲) ↪ V(G)` que fija `V(J)`) | `IsGlobalEmbedding` | `V(⋃𝒲) = (⋃_{H∈ℋ} V(H)) ⊔ {(H,i)}` | `isGlobalEmbedding_iff` | sí | definición |
| [P25] | Nociones del proyecto | `IsPiecewiseHostEmbedding`, `NewEdgesDistinct` | inyectividad por pieza; imágenes distintas de las aristas nuevas | `IsGlobalEmbedding.injective_piece`, `IsGlobalEmbedding.newEdgesDistinct` (global ⇒ ambas) | sí | EFD (comparaciones) |
| [P25] | **Lema 3.8, lectura literal** | `GeneralEmbeddingLemmaLiteral`, **`not_generalEmbeddingLemmaLiteral`** | — | — | sí | **refutado** (se demuestra su negación) |
| [P25] | Lema 3.8, variante por piezas | `GeneralEmbeddingLemmaPiecewise`, **`generalEmbedding_piecewise`** | inyectividad por pieza + aristas nuevas distintas | `generalEmbeddingLemmaPiecewise_iff` (`Iff.rfl` con `GeneralEmbeddingLemma`) | sí | **VD** |

## Notas por prioridad

### Prioridad 1: Teoremas 3.7 y 3.8 de [DP24]

* **Entrada.** `X` es un multihipergrafo `r`-uniforme cualquiera: un tipo de etiquetas `E` con
  `ends : E → Finset (Fin n)`, sin pedir inyectividad. Exijo `mult ends X e ≤ multBound q r` para
  todo `e` y `C ≤ n`, y `Y ⊆ Fin n` está prescrito con `n/3 ≤ |Y|`. No aparece `Δ(X) ≤ n/C`. Las
  multiplicidades no se pierden: la salida contiene `X.image g` con `g` inyectiva y
  `ends' (g c) = ends c`.
* **Planitud.** Es la de la Definición 3.6, `∀ e ∈ R, |e \ Y| ≤ r-1` (respectivamente `∀ e ∈ A`).
* **Relación entre ambos.** `theorem_3_8_conclusion` es incondicional. `theorem_3_8` deduce de él
  la forma inductiva exacta. `theorem_3_7_for_all` usa `theorem_3_8_conclusion`, y
  `theorem_3_8_conclusion_via_3_7` recorre la inducción del artículo con la hipótesis descargada
  por `theorem_3_7`.
* **Teorema 1.4 para multigrafos.** El artículo aplica el Teorema 1.4 a cada `H ∈ ℋ'`, que puede
  tener aristas paralelas. Aquí construyo ese absorbedor (`exists_multiGadget`): cada copia `c` se
  «mueve» con una clique privada `K_c` sobre `e_c ∪ N_c`, y un absorbedor simple de la biblioteca
  absorbe el grafo simple resultante.
* `Original2024.theorem_3_7_local` (versión local, con reserva y dispersión) sigue siendo una
  herramienta aparte. No lo identifico con el Teorema 3.7 completo.

### Prioridad 2: Definiciones 1.5–1.10 y Teoremas 1.7 y 1.11 de [DP24]

Las propiedades `oneX` (una arista de `X` por clique o por pieza), la cota de la familia `Δ(𝓗)` y
la igualdad de conjuntos ambiente son condiciones del propio artículo y están dentro de los
contratos. No son fortalecimientos nuevos.

### Prioridad 3: Definición 3.7 y Lema 3.8 de [P25]

* El texto impreso pide **inyectividad global** sobre `V(⋃𝒲)` fijando `V(J)`. `isGlobalEmbedding_iff`
  muestra que eso equivale a tres condiciones a la vez: inyectividad en cada pieza, imágenes
  disjuntas de los vértices nuevos de piezas distintas, y vértices nuevos que evitan todo
  `V(H')`, `H' ∈ ℋ`.
* **Obstrucción** (`not_generalEmbeddingLemmaLiteral`). Con esa lectura, el Lema 3.8 es **falso**.
  Tomemos `C = 3`, `r = 2`, `γ = 1/2` y cualquier `C'`. Sean `n = 2k ≥ max(4, C')`, `G = K_n^2`,
  `J` un emparejamiento perfecto, `ℋ` el conjunto de sus aristas individuales y `W_H` el triángulo
  sobre `H` con un vértice nuevo. Se cumplen todas las hipótesis: `Δ(J) = 1 ≤ n/C'`, `ℋ` es
  `3`-refinada, `𝒲` está `3`-acotado y es intersecante por aristas, y cada `W_H` tiene
  `n - 2 ≥ n/2` embeddings en `G \ (E(J) \ E(H))`. Sin embargo `V(J) = V(K_n)`, así que no queda
  ningún vértice libre para los vértices nuevos.
* El resultado existente (`generalEmbeddingLemma`) usa inyectividad por pieza y añade que las
  aristas nuevas son distintas. Aquí queda como **variante demostrada** (`generalEmbedding_piecewise`),
  no como transcripción literal. No añadí ninguna hipótesis que no esté en la fuente para «salvar»
  la lectura literal. No pude consultar la referencia [10] para confirmar qué noción usa la prueba
  original.

### Prioridad 4: Teorema 2.8, Teoremas 6.2 y 6.3, Lema 6.4 de [DP24]

* **Teorema 2.8**: el enunciado general está transcrito (`Theorem_2_8`), pero **no está demostrado**.
  Falta probar el nibble con reservas general para multihipergrafos `G₁ ⊔ G₂`. El
  `localNibble` del proyecto da emparejamientos pseudoaleatorios en hipergrafos simples casi
  regulares con conjuntos de prueba, pero no la fase de reservas (cubrir los vértices restantes de
  `A` con `G₂`). Además, `G₁` aquí no es casi regular fuera de `A` y puede tener aristas paralelas.
  La referencia [5] contiene la prueba y no pude consultarla.
* **Teorema 6.2** y **Teorema 6.3**: los enunciados están transcritos y siguen **abiertos**. El
  artículo deduce 6.2 de 6.3, y de 6.3 solo da un esbozo («We omit the details»). La ortogonalidad
  de la raíz de un booster no controla `|V(Q₁) ∩ V(Q₂)|` para todas las parejas, así que no la uso
  como certificado.
* **Lema 6.4**: **demostrado** (`lemma_6_4`).
