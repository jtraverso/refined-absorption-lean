# Ledger: Teoremas 2.8, 6.2 y 6.3 de arXiv:2402.17855v1 (ya demostrados)

En esta ronda se demostraron los tres resultados que quedaban pendientes del artículo de
Delcourt–Postle *Refined Absorption* (arXiv:2402.17855v1). Los enunciados son exactamente los
contratos que ya existían en `RequestProject/Faithful2024/`:

| Endpoint (nombre completo) | Tipo exacto | Archivo |
| --- | --- | --- |
| `RefinedAbsorption.Pending.theorem_2_8` | `RefinedAbsorption.Faithful2024.Theorem_2_8` | `RequestProject/Pending/Theorem28.lean` |
| `RefinedAbsorption.Pending.theorem_6_3` | `RefinedAbsorption.Faithful2024.Theorem_6_3` | `RequestProject/Pending/Theorem63Final.lean` |
| `RefinedAbsorption.Pending.theorem_6_2` | `RefinedAbsorption.Faithful2024.Theorem_6_2` | `RequestProject/Pending/Theorem62.lean` |

Comprobación (`checks/PendingEndpoints.lean`, salida en `checks/PendingEndpoints.out`):
- `#check` de los tres endpoints y `#print` de los tres contratos, que muestran sus tipos completos;
- `#print axioms` de cada endpoint: `[propext, Classical.choice, Quot.sound]`;
- `example : Faithful2024.Theorem_X := Pending.theorem_X` para los tres.

Ninguno de los tres teoremas tiene hipótesis adicionales: son constantes cerradas de los tipos
indicados. No hay `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` ni `unsafe` en
`RequestProject/Pending/`. `lake build` compila el proyecto completo.

## Preservación

- No se modificó ningún archivo existente. Todo el trabajo nuevo está en `RequestProject/Pending/`
  (namespace `RefinedAbsorption.Pending`), en `checks/PendingEndpoints.*`, en
  `checks/pending_integrity/` y en este ledger.
- `checks/pending_integrity/before_sha256.txt` (hashes de los 299 archivos versionados, tomados
  antes de editar) y `checks/pending_integrity/after_sha256.txt` (los mismos archivos al terminar)
  son idénticos.

## 1. Fuentes consultadas

- Delcourt–Postle, *Refined Absorption*, arXiv:2402.17855v1 (el PDF del proyecto): §2.2
  (enunciado de 2.8, que remite a [5]) y §6.3 (enunciados de 6.2 y 6.3, Lemma 6.4 y el esbozo de las
  "dos modificaciones" de la prueba de 6.1).
- Delcourt–Postle, arXiv:2204.08981 (v2 y v4, adjuntos): la idea del cierre tipo Lemma 3.4
  (una opción por vértice elegida al azar más el Lema Local, aquí con conjunto de configuraciones
  prohibidas vacío). **No** se identificó el Theorem 2.6 bipartito de esa referencia con el
  Teorema 2.8: la prueba Lean de 2.8 está hecha directamente sobre el contrato general
  (`G₁ ∪ G₂`, con `G₁` no necesariamente bipartito) y no usa ninguna transcripción de [5].
- No se usó el spread nibble de arXiv:2402.17858.

## 2. Pasos que el artículo omite o deja implícitos

### Teorema 2.8
El artículo solo enuncia 2.8 y remite a [5]; en [5] no aparece literalmente el contrato general.
Todo el argumento se formalizó aquí:
1. el nibble local para multihipergrafos etiquetados (copias paralelas conservadas), casi regular
   **solo** en `A`, mediante una regularización por capas que conserva los codegrados;
2. el control **ponderado** de la carga residual de cada `b ∈ B \ A`: pesos
   `w_b(a) ≤ codeg(a,b) ≤ D^{1-β}` con `∑ w_b ≤ D`, estratificados en conjuntos de nivel
   `T_{b,s}` (fórmula de la torta por capas). Los niveles grandes se controlan con el nibble y los
   pequeños de forma trivial;
3. el cierre con el Lema Local (sin elección voraz);
4. la unión de los dos matchings (disjuntos porque `V₁ ∩ V₂ = A`), con `A₀ = ∅` incluido;
5. la conversión de `D` real a `⌊D⌋` y la elección del umbral natural `D_β`.

### Teorema 6.3
El artículo dice "We omit the details". Detalles formalizados:
1. **Absorbedores:** las piezas privadas son absorbedores *root-light* (todo clique de cualquiera de
   los dos modos corta las raíces en `≤ r` vértices). Se obtienen de Lemma 6.4 en el modo con raíz
   y de la independencia de las raíces (`< r`) en el modo sin raíz. Se colocan con una versión del
   Lemma 5.2 que, además, evita que un `(r+1)`-subconjunto de un bloque del packing dado quede
   dentro de raíces ∪ auxiliares sin estar dentro de las raíces. En cada paso solo se excluyen
   `2^{k+h}·q` vértices, porque un `r`-conjunto está en a lo sumo un bloque. Con eso, ningún
   clique de la familia de descomposición del omni-absorbedor corta un bloque en `≥ r+1` vértices.
   El tamaño uniforme de la biblioteca root-light se obtiene sumando sobre los finitos `r`-grafos
   en `Fin k` (`k ≤ K`) y rellenando con vértices nuevos aislados.
2. **Nibble:** se eliminan los `q`-conjuntos peligrosos `dangerFam q r Q₁` tanto de la familia
   boosteada (fase principal) como de las cliques de reserva (fase de cierre de reservas, con
   `reserve_cover_multi` de una capa y familia prohibida arbitraria). La absorción final solo usa
   cliques de la familia del omni-absorbedor, que ya son seguras.
3. **Conteo crítico** (`cliqueMult_dangerFam_le`): cada `r`-conjunto está en a lo sumo
   `2^r · q · n^{q-r-1}` `q`-conjuntos peligrosos. La prueba estratifica por `A = P₀ ∩ e`, usa la
   unicidad del bloque que contiene un `r`-conjunto y trata por separado el caso en que no hay
   suficientes plazas (el conjunto forzado tiene más de `q` elementos), sin truncamientos de resta
   natural injustificados.
4. **Diferencia con el texto impreso:** el último párrafo de §6.3 en v1 dice
   "only `O(v(X)^{q−r+1})` such q-sets containing a fixed edge". Esa cota no es de orden inferior a
   `n^{q-r}`, así que no basta. Aquí se demuestra `O(n^{q-r-1})`, que es lo que de verdad se
   necesita (`ev_removal_poly`, `ev_reserve_slack_poly`).
5. `r = 1` se trata aparte de forma elemental (`theorem_6_3_one`): filas de longitud `q` que
   contienen los bloques, indexadas por `Fin k × Fin q`, y grupos `{(j,t) : j + t ≡ c (mod k)}`.

### Teorema 6.2
El artículo solo afirma que 6.2 "se deduce" de 6.3. La deducción formalizada: `L` va dentro del
conjunto `U` de los primeros `m'` vértices de `Fin (m+h)`, con `m' ≥ m` y `m+h` admisibles y `m+h`
grande. Se toma `A₀ = K_{m+h}^r \ K_U^r`, que es divisible, denso, disjunto de `L` y tiene `U`
independiente. 6.1 da `Q₁` (descomposición de `A₀`, y por tanto packing de `A₀ ∪ L`), y 6.3 da
`Q₂` (descomposición de `A₀ ∪ L` con las intersecciones cruzadas `≤ r`). Al final se transporta todo
por `Fin m ⊕ Fin h ≃ Fin (m+h)`, fijando los vértices de `L`. La construcción no usa 6.2.

## 3. Lemas técnicos formalizados en esta tarea (`RequestProject/Pending/`)

| Archivo | Contenido principal |
| --- | --- |
| `Closing.lean` | `closing_lll`: cierre tipo Lemma 3.4 con el Lema Local |
| `Regularize.lean` | `liftE`, `liftE_star`, `liftE_codeg`: regularización por capas sobre `ZMod M` |
| `MultiNibble.lean` | `multiNibbleA`: nibble local para multihipergrafos, casi regular solo en `A` |
| `Core28.lean` | `layer_cake`, `thm28_core`: núcleo combinatorio de 2.8 para un `D` fijo |
| `Theorem28.lean` | `thm28_eventually`, **`theorem_2_8`** |
| `SafeInner.lean` | `innerInv_step_avoid`: paso de Lemma 5.2 con un conjunto extra excluido |
| `SafeEmbed.lean` | `safePartialCliqueEmbedding`: Lemma 5.2 con la condición de seguridad |
| `Danger.lean` | `dangerFam`, `cliqueMult_dangerFam_le` (conteo `2^r q n^{q-r-1}`) |
| `SafeNibble.lean` | `safeNibbleWithReserves`: nibble con reservas que evita una familia dispersa |
| `RootLight.lean` | `rootLightLibrary`: biblioteca uniforme de absorbedores root-light (desde Lemma 6.4) |
| `SafeAbsorbers.lean` | `safePlacedAttachedAbsorbers`: absorbedores adjuntos seguros respecto de un packing |
| `SafeHost.lean` | `safeHostRefinerAbsorbers`, `safeHostCore`, `safeTheorem17`: Teorema 1.7 seguro |
| `Theorem63.lean` | `absorption_step_explicit`, `theorem_6_3_two_le` |
| `Theorem63One.lean` | `exists_partition_card`, `latin_groups`, `theorem_6_3_one` |
| `Theorem63Final.lean` | **`theorem_6_3`** |
| `Theorem62.lean` | **`theorem_6_2`** |

## 4. Dependencias (resultados ya demostrados en el proyecto que se reutilizan)

- 2.8: `Nibble.localNibble` (nibble local con conjuntos de prueba) y el Lema Local del directorio
  `Nibble/`.
- 6.3: `Original2024` (cadena de la prueba de 6.1: `relWeakReserves`, `boostLemma`,
  `clique_deg_conversion`, `eventually_parameter_bounds`, `placedMultiplicityReductionHost`,
  `General.nativeStrongMultiRefiners_all`, `omniAbsorber_of_refiner_absorbers`, `hostWitness_empty`,
  `mul_deg_compl_le`), `Placement` (Lemma 5.2 y sus invariantes), `Faithful2024.lemma_6_4`,
  `nibbleLeftoverDegreeSub_proved`, `reserve_cover_multi`.
- 6.2: `Original2024.theorem_6_1`, `theorem_6_3` (de esta tarea),
  `Extensions.exists_admissible_near`, `isDivisible_completeRGraph_iff`.

Todas estas dependencias están demostradas sin `sorry` (los `#print axioms` de los endpoints solo
muestran los tres axiomas estándar).

## 5. Pruebas completadas

- [x] `RefinedAbsorption.Pending.theorem_2_8 : RefinedAbsorption.Faithful2024.Theorem_2_8`
- [x] `RefinedAbsorption.Pending.theorem_6_3 : RefinedAbsorption.Faithful2024.Theorem_6_3`
- [x] `RefinedAbsorption.Pending.theorem_6_2 : RefinedAbsorption.Faithful2024.Theorem_6_2`

No quedan objetivos pendientes de esta ronda.
