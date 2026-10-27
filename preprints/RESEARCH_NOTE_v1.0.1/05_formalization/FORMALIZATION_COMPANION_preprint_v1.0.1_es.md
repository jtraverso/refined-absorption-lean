---
title: 'Formalización en Lean de la absorción refinada de Delcourt–Postle: complemento de formalización'
author: 'Juan Pablo Traverso Gianini'
email: 'jtraverso@gmail.com'
orcid: '0009-0003-6068-4096'
date: '27 de octubre de 2026'
---

**Complemento de** *Formalización en Lean de la absorción refinada de Delcourt–Postle*, nota de investigación, prepublicación 1.0.1.

**Prepublicación 1.0.1, 27 de octubre de 2026.**

**DOI de la versión 1.0.1:** [10.5281/zenodo.23715622](https://doi.org/10.5281/zenodo.23715622).

© 2026 Juan Pablo Traverso Gianini. Licencia [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

## Resumen

Este complemento permite localizar y reproducir las pruebas en Lean que acompañan la nota sobre Delcourt–Postle y la exposición de Postle. Relaciona los resultados citados con sus declaraciones formales, precisa sus hipótesis y registra las pruebas externas reutilizadas. Distingue el archivo formal original, con 316 fuentes, de la comparación unificada posterior, que añade una fuente y selecciona dieciocho declaraciones. El preflight completo de esa comparación pasó; su informe se conserva por separado de los trámites de revisión y registro en Palomar. El Apéndice A explica el contrato del omni-absorbedor y su cota de grado. Esta revisión sólo modifica los documentos: conserva las fuentes Lean y sus archivos de evidencia.

## 1. Fuentes matemáticas y alcance

Los dos textos principales son Delcourt–Postle [1], con base de enunciados arXiv:2402.17855v1, y Postle [2], formalizado a partir de arXiv:2510.19978v1. El identificador publicado de la exposición de Postle es DOI 10.1137/25M1805977, ICM 2026, volumen 6, páginas 212–231. Su Conjetura 1.1, Teorema 1.10, Definiciones 3.6–3.7 y Lema 3.8 se comprobaron en esa edición. Es una comprobación de los enunciados identificados, no de equivalencia entre todos los contenidos de ambas ediciones.

La formalización contiene los resultados principales de absorción, descomposición densa y existencia de diseños que se enumeran abajo. El resultado de índice arbitrario demuestra la existencia de familias simples de bloques para todos los $q>r\ge2$ y $\lambda\ge1$ fijos, en todos los órdenes admisibles suficientemente grandes. No está restringido al caso de Steiner. Las aplicaciones generales de cintura alta quedan fuera de este alcance congelado. Esta es una revisión documental intermedia; la versión definitiva prevista describirá la cobertura completa de los dos textos fuente una vez terminadas y auditadas las pruebas pendientes y sus dependencias.

Los autores de los teoremas fuente conservan la atribución matemática. La nota explica interfaces y deduce consecuencias de resultados demostrados. Se reconoce el trabajo clásico sobre intersecciones de sistemas triples [10,11]; no se reivindica prioridad histórica para cada consecuencia de parámetros generales. El resultado de Nash–Williams se atribuye a Delcourt–Postle [7], y la prueba formal reutilizada está documentada en [8,9].

## 2. Resultados canónicos

Las tablas identifican las dieciocho declaraciones de la comparación unificada. Sus tipos completos están en `Palomar/UnifiedChallenge.lean`; los intervalos y hashes de las extracciones anteriores se conservan en `provenance/palomar-extractions.json`. Cada nombre seleccionado aparece en las consultas de axiomas congeladas. La biblioteca también demuestra resultados que no forman parte de esta selección.

### 2.1. Artículo original

| Resultado fuente | Declaración canónica |
| --- | --- |
| [1, Teorema 1.7] | `RefinedAbsorption.Faithful2024.theorem_1_7` |
| [1, Teorema 1.11] | `RefinedAbsorption.Faithful2024.theorem_1_11` |
| [1, Teorema 6.1] | `RefinedAbsorption.Original2024.theorem_6_1` |
| [1, Teorema 2.8] | `RefinedAbsorption.Pending.theorem_2_8` |
| [1, Teorema 6.2], cláusula ambiente explícita | `RefinedAbsorption.Faithful2024.theorem_6_2_ambient` |
| [1, Teorema 6.3] | `RefinedAbsorption.Pending.theorem_6_3` |

Los dos primeros resultados conservan conjuntos explícitos de vértices del grafo ambiente y la distinción entre uso acotado de aristas, tamaño acotado de miembros y grado de refinamiento de una familia. El teorema de reserva usa copias etiquetadas de aristas, cotas de grados en las raíces designadas y la intersección ambiente indicada. No sustituye ese contrato por casi regularidad global ni por una cota del número de aristas.

El resultado anterior `RefinedAbsorption.Pending.theorem_6_2` sigue disponible. Su predicado de absorbedor usa el soporte de aristas del grafo antiguo. El resultado añadido también prohíbe una arista del absorbedor completamente contenida en el conjunto antiguo entero. Incluye etiquetas aisladas y permite aristas mixtas antiguas/nuevas. El espacio de nombres heredado `Pending` no significa que estos resultados demostrados sigan abiertos.

### 2.2. Exposición de Postle

| Fuente o precisión | Declaración canónica |
| --- | --- |
| [2, Teorema 1.10] | `RefinedAbsorption.Final.theorem_1_10` |
| [2, Conjetura 1.1], índice fijo al menos uno | `RefinedAbsorption.existenceConjecture_proved` |
| Especialización de existencia de Steiner | `RefinedAbsorption.Final.existenceConjecture_steiner` |
| Negación de la conclusión literal de encaje global | `RefinedAbsorption.FaithfulSurvey2025.not_generalEmbeddingLemmaLiteral` |
| Reemplazo por piezas demostrado | `RefinedAbsorption.FaithfulSurvey2025.generalEmbedding_piecewise` |

Las dos últimas filas son afirmaciones distintas. El predicado global usa los vértices antiguos que aparecen en las piezas indexadas. El testigo con emparejamiento perfecto cubre todos los vértices antiguos, por lo que también refuta la conclusión impresa sobre el conjunto antiguo completo. No se infiere de ese testigo una identidad definicional general entre todas las convenciones sobre vértices no utilizados.

Se siguió la referencia de prueba de la exposición de Postle [4, Apéndice B]. Su demostración existe; también escribe una inyección global. El teorema por piezas permite aplicaciones inyectivas separadas, con las condiciones sobre el grafo ambiente e imágenes distintas de aristas nuevas. No debe presentarse como una demostración de la afirmación global.

### 2.3. Nota de investigación

| Ubicación en la nota | Declaración canónica |
| --- | --- |
| Teorema 5.1 | `RefinedAbsorption.Extensions.steiner_completion_avoiding` |
| Corolario 5.2(i) | `RefinedAbsorption.Extensions.steiner_intersection_prescribed` |
| Corolario 5.2(ii) | `RefinedAbsorption.Extensions.partialSteiner_intersection_embedding` |
| Proposición 5.3 | `RefinedAbsorption.Extensions.steiner_intersection_spectrum_poly` |
| Teorema 6.2, todo sistema existente | `RefinedAbsorption.Assembly.steiner_quantitatively_almost_resolvable` |
| Teorema 6.2, existencia | `RefinedAbsorption.Assembly.exists_quantitatively_almost_resolvable_steiner` |
| Teorema 6.3 | `RefinedAbsorption.Assembly.nash_williams_scheduled_decomposition` |

Los resultados de intersección están en `RefinedAbsorption/Extensions/Intersection.lean`. Usan el teorema de descomposición compatible, la completación dispersa usual y lemas de empaquetamientos finitos. Los tres resultados cuantitativos cerrados están en `RefinedAbsorption/Assembly.lean`. Sus predecesores condicionales se conservan sin cambios.

El Teorema 6.1 de la nota es el resultado de entrada `Pseudorandom.chromatic_index_polynomial`, de la fuente fijada que se describe en la Sección 4; no es una declaración adicional en la selección de dieciocho enunciados.

## 3. Cuantificadores y representación

Para completación e intersecciones dispersas prescritas se fijan primero $q>r\ge1$. La constante positiva de dispersión y el umbral de orden se eligen antes del orden ambiente y de los sistemas parciales. La dispersión se refiere a $\Delta_{r-1}(H(P))$, el $r$-grafo cubierto. El sistema parcial prohibido no tiene que ser disperso. La garantía adicional de cruce se restringe a bloques prohibidos cuyas $r$-aristas evitan $H(P)$.

Para existencia con índice arbitrario se fijan $q>r\ge2$ y $\lambda\ge1$ antes de elegir el umbral de orden. El umbral puede depender de los tres parámetros. La condición de admisibilidad usa ese índice; no se afirma un umbral uniforme para todos los índices.

Para el encaje como intersección exacta, un sistema parcial finito dado determina un umbral de orden. Todo orden admisible mayor admite una inyección y dos sistemas cuya familia común de bloques es precisamente la imagen de la familia dada. La inyección se elige junto con los sistemas; el resultado no cuantifica sobre toda inyección prescrita de antemano. El resultado de espectro elige ambos sistemas y da un intervalo inicial $0\le k\le c n^r$.

El resultado universal de coloreo de Steiner fija $q>r\ge2$ y después elige $\gamma,n_0$ antes de $n$ y del sistema de Steiner. La variante de existencia añade admisibilidad. Lean escribe el cociente de grado de puntos como división natural antes de convertirlo a reales:
$$
R=\frac{\binom{n-1}{r-1}}{\binom{q-1}{r-1}}.
$$
La prueba de conteo establece divisibilidad exacta para un sistema de Steiner, por lo que éste es el grado ordinario de puntos, y no una aproximación por piso. La aplicación formal de colores está definida sobre conjuntos finitos de vértices y se restringe en los bloques del sistema. Su número de etiquetas satisface
$$
R\le m\le R+R^{1-\gamma}.
$$
Se permiten etiquetas no usadas. Por eso la nota afirma una cota superior para el número de clases paralelas parciales y justifica la cota inferior por separado.

Para la aplicación a grafos existen constantes universales $\gamma,n_0$ antes del grafo finito. Las hipótesis son divisibilidad en triángulos, orden suficientemente grande y la desigualdad exacta
$$
3n\le4\delta(G).
$$
La salida es una descomposición efectiva en triángulos y un coloreo propio de su hipergrafo de triángulos, con
$$
\Delta(G)/2\le m
\le\Delta(G)/2+(\Delta(G)/2)^{1-\gamma}.
$$
No aparece una hipótesis de casi regularidad del grafo, un teorema externo como premisa ni una conclusión de factores que abarquen todos los vértices. Ambas aplicaciones cuantitativas tienen $0<\gamma<1$.

Los tipos finitos y las instancias de igualdad decidible son parámetros de representación. Los contratos seleccionados usan tipos finitos ordinarios en el universo cero. Las familias de bloques son conjuntos finitos, por lo que el resultado de existencia para índice fijo no permite repetir bloques. El nombre `steiner_orthogonal_mate` en otra parte de la biblioteca significa intersecciones cruzadas acotadas y ausencia de bloques comunes; no afirma ortogonalidad clásica de Steiner.

## 4. Ensamblaje de pruebas externas

La revisión fijada de Pippenger–Spencer es

`b19273396d369332fb489fe07e61e27c9e7f9233`

en `jtraverso/pippenger-spencer`. El subconjunto de fuentes incorporado contiene `Basic.lean`, `ColourHypergraph.lean` y `Polynomial.lean` bajo `RefinedAbsorption/Upstream/PippengerSpencer/`. Sólo cambiaron las rutas de importación y los finales de línea. Se verificó la identidad de diecinueve fuentes compartidas de emparejamiento tras sustituir el prefijo de importación, y se reutilizan desde la dependencia Nash–Williams. Los hashes originales e instalados, incluida la normalización CRLF/LF, están registrados en `provenance/assembly-sources.json`.

El resultado de coloreo polinómico es `Pseudorandom.chromatic_index_polynomial`. Se demuestra a través del resultado de Ehard–Glock–Joos [6], usando un hipergrafo auxiliar de colores y una completación. Su contrato exacto incluye grado máximo, cogrados polinómicos y una cota exponencial del número de aristas. No tiene condición inferior de grados. Esto no afirma que [5] imprima esa formulación cuantitativa exacta.

La dependencia Nash–Williams es `jtraverso/nash-williams-lean` en

`2603197abdbf0a600ec663f6f046f70fbd209d4a`.

El resultado efectivamente utilizado es `NashWilliams18.PaperI.nash_williams_via_paperII`, importado desde `RequestProject.NW18.PaperIIAssembly`. El módulo local `RefinedAbsorption.ExternalProofs` proporciona ambos contratos mediante aplicación directa de esos resultados demostrados. Por tanto, las tres declaraciones finales de `RefinedAbsorption.Assembly` no tienen ninguna de las dos hipótesis de teorema externo.

La raíz local de módulos se trasladó de `RequestProject` a `RefinedAbsorption` para evitar una colisión con las rutas de la dependencia. Se conservaron los espacios de nombres de las declaraciones matemáticas. El repositorio incluye la licencia del fragmento de fuentes y los registros de correspondencia.

## 5. Compilación, axiomas y conservación

El commit de fuente formal es

`5428ee9b772e67dd7ec6da443199b36a003b72d4`.

Lo identifica la etiqueta local de fuente formal `formal-v1.0`. El toolchain es `leanprover/lean4:v4.35.0-rc3`; Mathlib está fijado en

`c55e6e786f49471c72fbddbec5415808896aec1e`.

El manifiesto fija diez dependencias Git, incluida Nash–Williams. Se comprobaron las revisiones efectivas de sus checkouts y la ausencia de cambios en archivos versionados. Los objetivos de compilación por defecto de Lake son `RefinedAbsorption`, `checks` y `Palomar`. La raíz agregada importa transitivamente los 299 módulos de la biblioteca local; junto con la raíz son 300 fuentes. La compilación congelada añade diez módulos de comprobación y seis archivos independientes de comparación, para un total de 316 fuentes. La comparación unificada posterior lleva el total actual a 317.

La campaña comenzó sin el directorio de compilación del proyecto y reutilizó las cachés de dependencias fijadas. Las compilaciones por grupos se reanudaron hasta completar la biblioteca y los módulos de comprobación; después se compilaron las seis interfaces de comparación y se completó la compilación por defecto. Se registra así una compilación limpia del proyecto, no de todas sus dependencias desde cero. Los intentos fallidos y sus correcciones, entre ellas la posición de un comentario de módulo y la lectura UTF-8 de los registros en Windows, permanecen en `publication/assembly/`. Son parte de la historia de compilación, no hipótesis adicionales de las pruebas.

Una vez guardados los archivos en Git, el validador del archivo congelado comparó las fuentes y la configuración con ese commit, comprobó su vigencia y las trazas de Lake, y registró los hashes de fuentes y artefactos. La tabla siguiente recoge las consultas de axiomas.

| Módulo de comprobación | Consultas |
| --- | ---: |
| `AxiomCheck` | 290 |
| `ExtensionsAxioms` | 14 |
| `FaithfulAxioms` | 13 |
| `IntersectionAxioms` | 11 |
| `Original2024Axioms` | 14 |
| `PendingAxioms` | 2 |
| `PendingEndpoints` | 3 |
| `QuantitativeAxioms` | 7 |
| `AssemblyAxioms` | 5 |
| `SourceFidelityAxioms` | 1 |
| Total | 360 |

Son consultas, sin afirmar que haya 360 nombres de teoremas distintos. Las salidas contienen sólo `propext`, `Classical.choice` y `Quot.sound`, o ningún axioma. El desarrollo de pruebas conservado no tiene huecos pendientes ni axiomas del proyecto. Los cuatro archivos `Palomar/*Challenge.lean` contienen 36 huecos de prueba con `sorry` por diseño: seis, siete, cinco y dieciocho en los archivos Article2024, ResearchNote, Survey2025 y Unified, respectivamente. Si se incluye una mención en un comentario de cada archivo, resultan 40 apariciones textuales. Los módulos de biblioteca, comprobación y Solution no contienen ninguna. La Solution proporciona las pruebas y no importa el Challenge. Sería incorrecto decir «sin axiomas».

Se conservan las 300 fuentes Lean originales retornadas. La comparación de migración no informa diferencias textuales en encabezados de declaraciones ni cambios en 821 intervalos de declaraciones no demostrativas normalizados respecto de comentarios y espacios. El traslado posterior de imports conserva las 301 fuentes migradas salvo la sustitución documentada de prefijos. Son controles textuales, no un teorema de equivalencia de kernel entre versiones. El registro anterior de migración mediante Lean directo, con 301 fuentes y 354 consultas, permanece como evidencia histórica y no reemplaza el certificado final de Lake.

## 6. Archivo y reproducción

El archivo formal inmutable es

`publication/formal-freeze/formal-v1.0-5428ee9b772e.tar.gz`,

con SHA-256

`e9bb21b17a110a392a7751afefb9a2e9d6bf218c7e6dac788006234f3af09c05`.

Contiene el commit de fuente y la evidencia completa de compilación. El recibo externo `FREEZE.json` y el archivo adjunto de comprobación SHA identifican ese archivo. El registro de validación `publication/assembly/VALIDATION.json` tiene SHA-256

`45321434a170482d8473182ecc8c1fd60b66a84bb9480ef7f6c26f9f2b130157`.

Desde el checkout completo de publicación, `python tools/verify_formal_freeze.py` comprueba la correspondencia de fuentes actuales y archivadas, la integridad del archivo, el archivo de fuentes originales y los registros de axiomas registrados. No ejecuta Lean ni reproduce independientemente las pruebas. El archivo formal no puede contener su propio recibo con hash; para ese verificador de conveniencia se usa el checkout completo de publicación.

Para reconstruir las pruebas desde cero, se usa un checkout separado del commit de fuente formal o se extrae el archivo formal, se instala el toolchain de Lean fijado y se ejecuta:

```sh
lake exe cache get
lake build
```

El manifiesto público usa revisiones Git inmutables. Las rutas locales de overrides usadas en la campaña registrada de Windows están ignoradas por Git y no se necesitan en esta configuración portable. Los hashes de artefactos compilados describen la plataforma registrada; una reconstrucción en otra plataforma no tiene por qué reproducir esos bytes binarios.

Los manuscritos se mantienen en Markdown inglés y español, y después se convierten con la plantilla de la serie Nash–Williams del autor a TeX final y PDF. La inspección de páginas renderizadas, la paridad bilingüe y los hashes documentales están separados del freeze de fuentes formales. Commits posteriores de documentos y metadatos pueden conservar los bytes congelados de Lean y configuración; los commits exactos de publicación y registro se anotan en sus propios recibos.

## 7. Comparación, revisión y reutilización

Palomar [21] es un registro de resultados matemáticos formalizados. Un Challenge es un archivo de enunciados que se comparan; una Solution proporciona sus pruebas. La interfaz de comparación especifica esos archivos y las declaraciones seleccionadas. Un preflight es una verificación preliminar. NanoDa [22] y con-ron [23] son implementaciones adicionales de kernel usadas para comprobar las declaraciones exportadas. Los hashes exactos de sus binarios y la revisión del proceso utilizada aquí están en el informe mecánico archivado.

La entrada unificada usa `Palomar/Unified.comparator.json`, los metadatos `Palomar/Unified/formalization.yaml`, el Challenge `Palomar.UnifiedChallenge` y la biblioteca `RefinedAbsorption` como Solution. Reúne las dieciocho declaraciones de la Sección 2. Las configuraciones `Palomar/Article2024.comparator.json`, `Palomar/Survey2025.comparator.json` y `Palomar/ResearchNote.comparator.json` se conservan como vistas históricas de la misma selección.

El Challenge importa sólo Mathlib. Sus definiciones tienen cuerpos completos y sus dieciocho teoremas tienen huecos intencionales para expresar los enunciados que se comparan. La Solution importa las pruebas y no importa el Challenge. No se usan esos huecos como premisas de las demostraciones.

El commit de la comparación unificada es

`867d1e3d5e48ef20a8f1ae68237834eb06211cbc`.

Su verificación preliminar oficial completa, ejecución `40478830948`, terminó con resultado satisfactorio y sin errores el 27 de octubre de 2026 a las 10:18 UTC. El informe registra dieciocho teoremas seleccionados, 317 fuentes comprobadas y aceptación por NanoDa y con-ron. La advertencia sobre el tamaño recomendado del Challenge se conserva en el informe; no se excede su límite obligatorio. Los datos están en `publication/palomar/OFFICIAL_PREFLIGHT.json` y en el informe mecánico allí identificado.

El envío posterior tiene identificador `jne18fh5pbug`. El recibo local consultado, fechado el 27 de octubre de 2026 a las 11:59 UTC, registra el estado `verifying`. Es una observación histórica, no una consulta en vivo. Un preflight satisfactorio y un recibo de envío no acreditan por sí solos la revisión editorial ni el registro final. Esta revisión documental no modifica el envío ni sus recibos.

Las contribuciones del autor a Lean Pool [17] aportan otro antecedente de esta forma de trabajo. Las contribuciones del nibble finito y de desigualdades de concentración fueron incorporadas al repositorio principal. Se citan como desarrollos relacionados, no como dependencias importadas por esta biblioteca. El código que sí se reutiliza aquí se identifica en la Sección 4: su procedencia y sus revisiones forman parte de la evidencia reproducible.

La auditoría interna de los documentos fue realizada por Codex bajo la dirección del autor. Se distingue de las revisiones externas solicitadas y de una revisión independiente por pares humanos. La responsabilidad matemática y editorial corresponde al autor.

## Apéndice A. El contrato disponible del omni-absorbedor

La declaración `RefinedAbsorption.Faithful2024.theorem_1_7` ya permite usar el omni-absorbedor como resultado independiente de su demostración. Para $q>r\ge1$ fijos proporciona $C\ge1$ y $0<\varepsilon<1$. Si $G$ es un $r$-grafo sobre $n$ vértices y $X$ es un subgrafo generador de $G$, las hipótesis de grado son
$$
\delta_{r-1}(G)\ge(1-\varepsilon)n,
\qquad \Delta_{r-1}(X)\le n/C.
\tag{A.1}
$$
La salida incluye un omni-absorbedor $A\subseteq G$, disjunto de $X$ en aristas, sobre el mismo conjunto de vértices, con
$$
\Delta_{r-1}(A)\le C\max\{\Delta_{r-1}(X),\,n^{1-1/r}\log n\}.
\tag{A.2}
$$
La familia de descomposición está formada por cliques de tamaño $q$ en $X\cup A$, cada uno con a lo sumo una arista de $X$. Cada arista de $X\cup A$ aparece en a lo sumo $C$ miembros de esa familia. Para cada residuo divisible $L\subseteq X$, la función de descomposición selecciona de ella una descomposición de $A\cup L$. La divisibilidad se exige al residuo que se absorbe; no se añade como hipótesis de construcción a todo $X$.

La cota (A.2) es la que se formalizó. Su término adicional depende del orden del grafo y no puede omitirse al citar el resultado. Si $\Delta_{r-1}(X)\ge n^{1-1/r}\log n$, el máximo se reduce al primer término. El teorema no afirma esa desigualdad adicional para todo subgrafo disperso. La planitud corresponde a la etapa de multi-refinadores: `RefinedAbsorption.Faithful2024.Theorem_3_8_conclusion` la expresa mediante `RefinedAbsorption.Original2024.IsFlatTo`. No debe añadirse como una cláusula de la salida del omni-absorbedor. Del mismo modo, las multiplicidades de las copias etiquetadas y el número de miembros de la familia que usan una arista son datos distintos.

## Agradecimientos

El autor agradece profundamente a su esposa María Paz y a sus hijos Lucas, Juan Cristóbal, Francisca, Raimundo y Benjamín su amor, paciencia y apoyo.

## Uso de inteligencia artificial y herramientas computacionales

Claude, de Anthropic, y ChatGPT/Codex, de OpenAI, se utilizaron para explorar y comprobar argumentos y para preparar el manuscrito. Aristotle, de Harmonic, contribuyó a la exploración de enfoques, la búsqueda de contraejemplos, el desarrollo de demostraciones y su formalización y revisión en Lean. Su función no se limitó a traducir pruebas ya terminadas.

Certo [14] y Jacobian [15] se utilizaron para explorar casos finitos, comprobar identidades y evaluar construcciones candidatas. Estos cálculos orientaron el desarrollo de los argumentos; las comprobaciones finitas no se trataron como pruebas de enunciados universales.

El autor es responsable de los argumentos, las citas, el código y la exposición. Ningún sistema de IA figura como autor.

## Referencias

[1] M. Delcourt and L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture*, arXiv:2402.17855v1 (2024). <https://doi.org/10.48550/arXiv.2402.17855>.

[2] L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture and Its Applications to Extremal and Probabilistic Design Theory*, Proceedings of the International Congress of Mathematicians 2026, Volume 6, 212–231. <https://doi.org/10.1137/25M1805977>. Base de enunciados: arXiv:2510.19978v1 (2025), <https://doi.org/10.48550/arXiv.2510.19978>.

[3] M. Delcourt and L. Postle, *Finding an Almost Perfect Matching in a Hypergraph Avoiding Forbidden Submatchings*, arXiv:2204.08981 (2022). <https://doi.org/10.48550/arXiv.2204.08981>.

[4] M. Delcourt, C. Henderson, T. Lesgourgues and L. Postle, *Erdős meets Nash-Williams*, arXiv:2507.23624v1 (2025), Appendix B. <https://doi.org/10.48550/arXiv.2507.23624>.

[5] N. Pippenger and J. Spencer, *Asymptotic behavior of the chromatic index for hypergraphs*, Journal of Combinatorial Theory, Series A 51 (1989), 24–42. <https://doi.org/10.1016/0097-3165(89)90074-5>.

[6] S. Ehard, S. Glock and F. Joos, *Pseudorandom hypergraph matchings*, Combinatorics, Probability and Computing 29(6) (2020), 868–885. <https://doi.org/10.1017/S0963548320000280>.

[7] M. Delcourt and L. Postle, *A Proof of Nash-Williams' Conjecture*, arXiv:2606.11178v1 (2026). <https://doi.org/10.48550/arXiv.2606.11178>.

[8] J. P. Traverso Gianini, *Triangle decompositions I: Formalizing the Nash–Williams theorem in Lean*, preprint 1.0 (2026). <https://doi.org/10.5281/zenodo.23428173>.

[9] J. P. Traverso Gianini, *Triangle decompositions II: Robust absorption for typed triangles*, preprint 1.0 (2026). <https://doi.org/10.5281/zenodo.23502224>.

[10] C. C. Lindner and A. Rosa, *Steiner triple systems having a prescribed number of triples in common*, Canadian Journal of Mathematics 27(5) (1975), 1166–1175. <https://doi.org/10.4153/CJM-1975-122-4>.

[11] C. C. Lindner and A. Rosa, *Steiner triple systems having a prescribed number of triples in common (corrigendum)*, Canadian Journal of Mathematics 30(4) (1978), 896. <https://doi.org/10.4153/CJM-1978-077-9>.

[12] L. de Moura and S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, Automated Deduction — CADE 28 (2021), 625–635. <https://doi.org/10.1007/978-3-030-79876-5_37>.

[13] The mathlib Community, *The Lean Mathematical Library*, Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (2020), 367–381. <https://doi.org/10.1145/3372885.3373824>.

[14] J. P. Traverso Gianini, *Certo: computational tools with verifiable certificates*. Repositorio de software (2026), <https://github.com/jtraverso/certo-math>. Consulta: 27 de octubre de 2026; no se registró la versión exploratoria utilizada.

[15] Morluto and contributors, *Jacobian: composable mathematical tools*. Repositorio de software, <https://github.com/morluto/jacobian>. Consulta: 27 de octubre de 2026; no se registró la versión exploratoria utilizada.

[16] J. P. Traverso Gianini, *The Pippenger–Spencer theorem in Lean 4*. Repositorio de software, <https://github.com/jtraverso/pippenger-spencer>. Commit `b19273396d369332fb489fe07e61e27c9e7f9233` (2026).

[17] J. P. Traverso Gianini, *Contributions to Lean Pool* (2026). <https://github.com/jtraverso/lean-pool>. Contribuciones relacionadas: <https://github.com/LeanPool/lean-pool/pull/471>, <https://github.com/LeanPool/lean-pool/pull/431>. Ambas incorporadas al proyecto original; comprobación: 27 de octubre de 2026.

[18] P. Keevash, *The existence of designs*, arXiv:1401.3665 (2014), version 4 (2024). <https://doi.org/10.48550/arXiv.1401.3665>.

[19] S. Glock, D. Kühn, A. Lo and D. Osthus, *The Existence of Designs via Iterative Absorption: Hypergraph F-Designs for Arbitrary F*, Memoirs of the American Mathematical Society 284, no. 1406 (2023). <https://doi.org/10.1090/memo/1406>.

[20] M. Molloy and B. Reed, *Near-optimal list colorings*, Random Structures & Algorithms 17(3–4) (2000), 376–402. <https://doi.org/10.1002/1098-2418(200010/12)17:3/4%3C376::AID-RSA10%3E3.0.CO;2-0>.

[21] Palomar Registry, *About Palomar* (2026). <https://palomar-registry.org/about>.

[22] NanoDa contributors, *nanoda_lib: external type checker for Lean 4*. <https://github.com/ammkrn/nanoda_lib>.

[23] Lean contributors, *con-ron*. <https://github.com/leanprover/con-ron>.
