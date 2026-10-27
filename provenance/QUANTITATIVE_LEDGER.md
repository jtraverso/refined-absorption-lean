# Ledger de las extensiones cuantitativas (ronda posterior a 6a712935)

Entorno: Lean `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0` (commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`, según `lake-manifest.json`).

## 1. Archivos nuevos (ningún archivo anterior ha cambiado)

| Archivo | Contenido |
|---|---|
| `RequestProject/Extensions/PolynomialExternal.lean` | Solo **definiciones**: contratos externos `PippengerSpencerPolynomial`, `NashWilliamsExternal` y su vocabulario |
| `RequestProject/Extensions/PolynomialTools.lean` | Lemas genéricos demostrados (cota inferior de colores, doble conteo, `C·D² ≤ exp(D^γ)`, monotonía del error) |
| `RequestProject/Extensions/PolynomialResolution.lean` | Parte B: Steiner, todo sistema + corolario de existencia |
| `RequestProject/Extensions/NashWilliamsSchedule.lean` | Parte C: Nash–Williams con rondas |
| `checks/QuantitativeAxioms.lean`, `checks/QuantitativeAxioms.out` | `#check` y `#print axioms` de los tres endpoints, y su salida |
| `checks/quantitative_integrity/{before,after,new_files}_sha256.txt` | Hashes SHA-256 |

**Integridad.** `before_sha256.txt` (289 archivos versionados, tomados antes de cualquier cambio) y
`after_sha256.txt` (los mismos 289 archivos tras el trabajo) son **idénticos**. Así que
`Original2024`, `Final`, `Faithful2024`, `FaithfulSurvey2025`, `Extensions/AlmostResolvable.lean`
(incluidos `PippengerSpencer`, `steiner_almost_resolvable` y `exists_almost_resolvable_steiner` con ε) y
las demás interfaces siguen sin tocar. Los hashes de los archivos nuevos están en
`new_files_sha256.txt`.

**Build.** `lake build` (objetivo por defecto, que incluye todos los módulos `RequestProject.+`,
también los cuatro nuevos): *Build completed successfully (8301 jobs)*, sin errores.
`lake env lean checks/QuantitativeAxioms.lean`: terminó sin errores; la salida está en
`checks/QuantitativeAxioms.out`. Los archivos nuevos no contienen `sorry`, `admit`,
`native_decide`, `implemented_by`, `unsafe` ni declaraciones `axiom`.

## 2. Contratos externos (definiciones `Prop`, NO demostradas aquí)

Namespace `RefinedAbsorption.External`.

### `PippengerSpencerPolynomial : Prop`
Fuente: `jtraverso/pippenger-spencer@b19273396d369332fb489fe07e61e27c9e7f9233`, `Solution.lean`,
`PippengerSpencer.chromatic_index_polynomial`.
```
∀ (k : ℕ), 2 ≤ k → ∀ (δ : ℝ), 0 < δ → δ < 1 →
  ∃ γ : ℝ, 0 < γ ∧ ∃ D₀ : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V))
    (D : ℝ), D₀ ≤ D → IsUniform H k → (∀ v, (degree H v : ℝ) ≤ D) →
    (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ D ^ (1 - δ)) →
    (H.card : ℝ) ≤ Real.exp (D ^ γ) →
    ∃ (m : ℕ) (c : Finset V → Fin m), (m : ℝ) ≤ D + D ^ (1 - γ) ∧ IsProperEdgeColouring H m c
```
`IsUniform`, `degree`, `codegree` e `IsProperEdgeColouring` (namespace
`RefinedAbsorption.External.PippengerSpencer`) tienen los mismos cuerpos que en el archivo externo:
`degree` y `codegree` cuentan aristas. Se mantienen todos los cuantificadores y la cota
`|H| ≤ exp(D^γ)`. No se exige casi regularidad ni cota inferior de grado.
Adaptadores demostrados hacia el vocabulario del proyecto:
`degree_eq_deg_singleton : degree H v = deg H {v}` y
`codegree_eq_deg_pair : codegree H u v = deg H {u, v}`.

### `NashWilliamsExternal : Prop`
Fuente: `jtraverso/nash-williams-lean@2603197abdbf0a600ec663f6f046f70fbd209d4a`,
`Challenge.lean` (definiciones) y `Solution.lean` (`NashWilliamsTheorem.nash_williams`).
```
∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
  N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
    3 * Fintype.card V ≤ 4 * G.minDegree → NashWilliams.HasTriangleDecomposition G
```
`IsTriangle`, `IsTriangleDecomposition`, `HasTriangleDecomposition` e `IsTriangleDivisible`
(namespace `RefinedAbsorption.External.NashWilliams`) tienen los mismos cuerpos que en
`Challenge.lean`.

## 3. Teoremas nuevos (demostrados bajo las hipótesis explícitas)

Axiomas de los tres endpoints: `[propext, Classical.choice, Quot.sound]`. **Atención:** que los
axiomas sean estándar no significa que `hPSPoly` y `hNW` estén descargadas. Siguen siendo
parámetros del teorema.

| Declaración | Hipótesis externas | Estado |
|---|---|---|
| `RefinedAbsorption.Extensions.steiner_quantitatively_almost_resolvable` | `hPSPoly` | demostrado (condicional) |
| `RefinedAbsorption.Extensions.exists_quantitatively_almost_resolvable_steiner` | `hPSPoly` | demostrado (condicional) |
| `RefinedAbsorption.External.nash_williams_scheduled_decomposition` | `hPSPoly`, `hNW` | demostrado (condicional) |

Tipos completos (como los imprime `#check`, con `R := ↑((n-1).choose (r-1)) / ↑((q-1).choose (r-1))`):

```
steiner_quantitatively_almost_resolvable : ∀ {q r : ℕ}, PippengerSpencerPolynomial → 2 ≤ r → r < q →
  ∃ γ, 0 < γ ∧ γ < 1 ∧ ∃ n₀, ∀ n ≥ n₀, ∀ (𝒮 : Finset (Finset (Fin n))), IsSteinerSystem q r 𝒮 →
    ∃ m c, R ≤ ↑m ∧ ↑m ≤ R + R ^ (1 - γ) ∧ ∀ B ∈ 𝒮, ∀ B' ∈ 𝒮, B ≠ B' → c B = c B' → Disjoint B B'

exists_quantitatively_almost_resolvable_steiner : ∀ {q r : ℕ}, PippengerSpencerPolynomial → 2 ≤ r → r < q →
  ∃ γ, 0 < γ ∧ γ < 1 ∧ ∃ n₀, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
    ∃ 𝒮, IsSteinerSystem q r 𝒮 ∧
      ∃ m c, R ≤ ↑m ∧ ↑m ≤ R + R ^ (1 - γ) ∧ ∀ B ∈ 𝒮, ∀ B' ∈ 𝒮, B ≠ B' → c B = c B' → Disjoint B B'

nash_williams_scheduled_decomposition : PippengerSpencerPolynomial → NashWilliamsExternal →
  ∃ γ, 0 < γ ∧ γ < 1 ∧ ∃ n₀, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G → 3 * Fintype.card V ≤ 4 * G.minDegree →
      ∃ T, NashWilliams.IsTriangleDecomposition G T ∧
        ∃ m c, PippengerSpencer.IsProperEdgeColouring T m c ∧
          ↑G.maxDegree / 2 ≤ ↑m ∧ ↑m ≤ ↑G.maxDegree / 2 + (↑G.maxDegree / 2) ^ (1 - γ)
```

Observaciones de alcance:
* En el teorema para todo sistema de Steiner, `γ` y `n₀` dependen solo de `q`, `r` y del teorema
  externo. No se añade admisibilidad, ni `q ∣ n`, ni resolución exacta. Las clases de color son
  emparejamientos parciales. La admisibilidad (`DesignDivisibility n q r 1`) aparece solo en el
  corolario de existencia, que usa `steiner_exists` (ya demostrado en el proyecto).
* En Nash–Williams, `T` es una descomposición exacta (cada arista en exactamente un triángulo),
  `Δ(G) = G.maxDegree` del grafo original, y cada ronda está formada por triángulos disjuntos en
  vértices. No se impone casi regularidad.

### Ruta de las pruebas
**Steiner** (`D = R`, `δ = 1/(2(r-1))`, `k = q`):
* `steiner_regular_data`: todos los puntos tienen grado `a`, `R = a`,
  `codeg·(n-1) = a(q-1)`, `n-1 ≤ a(q-1)` y `a ≤ (n-1)^(r-1)`. Reutiliza `steiner_deg_point_mul`,
  `steiner_deg_pair_mul` y `steiner_codeg_mul`.
* `rpow_inv_two_pred_le_sqrt`: `a^δ ≤ √(n-1)`. Con `(q-1)² ≤ n-1` y `codeg_le_rpow_aux` se obtiene
  `codeg ≤ a^(1-δ)`.
* Doble conteo `q|𝒮| = n·a` (`uniform_card_mul_eq_sum_degree`), `card_le_mul_sq_aux`:
  `|𝒮| ≤ q·a²`. `eventually_mul_sq_le_exp_rpow` da entonces `|𝒮| ≤ exp(a^γ₀)` **para el exponente
  `γ₀` que efectivamente se pasa al teorema externo**.
* `a ≥ (n-1)/(q-1)`, así que para `n` grande `a ≥ max(D₀, D₁, 1)`; en particular `R ≥ 1`.
* Reducción del exponente: `γ = min γ₀ (1/2) ∈ (0,1)`. Como `R ≥ 1` y `γ ≤ γ₀`, se tiene
  `R^(1-γ₀) ≤ R^(1-γ)` (`rpow_error_mono`).
* La cota inferior viene de `resolution_classes_lower`.

**Nash–Williams** (`k = 3`, `D = Δ(G)/2`, `δ = 1/2`):
* `two_mul_degree_of_isTriangleDecomposition`: `2·degree T v = G.degree v`.
  `codegree_le_one_of_isTriangleDecomposition`: `codegree T u v ≤ 1` para `u ≠ v`. Son lemas
  reutilizables para cualquier descomposición dada.
* `3n ≤ 4δ(G) ≤ 4Δ(G)` da `D ≥ 3n/8`. Para `n ≥ 3` se tiene `D ≥ 1`, luego
  `codeg ≤ 1 ≤ D^(1/2)`. Para `n` grande, `D ≥ D₀`.
* `3|T| = Σ_v degree T v ≤ nD` y `n ≤ 8D/3`, así que `|T| ≤ 3D² ≤ exp(D^γ₀)`.
* La cota inferior se obtiene en un vértice de grado máximo
  (`degree_le_of_isProperEdgeColouring`). La superior usa `γ = min γ₀ (1/2)` como antes.

## 4. Adaptadores pendientes para el ensamblaje local

1. **Pippenger–Spencer.** Una vez importado `PippengerSpencer` del repositorio externo:
   `hPSPoly : PippengerSpencerPolynomial :=
     fun k hk δ h0 h1 => PippengerSpencer.chromatic_index_polynomial k hk δ h0 h1`.
   Por la igualdad literal de cuerpos, `IsUniform`, `degree`, `codegree` e
   `IsProperEdgeColouring` deberían unificar por `rfl`/`Iff.rfl`. Si el elaborador no los
   identifica (son constantes distintas en namespaces distintos), basta un `simp only` desplegando
   ambas definiciones o un lema puente `Iff.rfl` para cada una.
2. **Nash–Williams.** `hNW : NashWilliamsExternal := NashWilliamsTheorem.nash_williams`, con el
   mismo comentario: `NashWilliams.IsTriangleDivisible` y `HasTriangleDecomposition` del repositorio
   externo frente a las copias de `RefinedAbsorption.External.NashWilliams`. Hay que desplegar las
   definiciones; las instancias (`DecidableRel G.Adj`, `Fintype`) son las mismas.
3. **Compatibilidad de versiones.** Hay que comprobar que ambos repositorios compilan con Lean
   `v4.28.0` y Mathlib `8f9d9cff…`. Si usan otra revisión, se necesitará migrar o fijar una común.
   Esto no se ha comprobado aquí: no se ha importado ninguna biblioteca externa.

## 5. Lo que sigue abierto (sin cambios)
`Theorem_2_8`, `Theorem_6_2` y `Theorem_6_3` siguen siendo enunciados abiertos, no pruebas. No se
declaran completos los dos papers. Se mantiene la separación del survey:
`GeneralEmbeddingLemmaLiteral` está refutada (su negación está demostrada) solo como lectura
global formalizada. La intención del autor y la referencia [10] siguen sin verificarse.
