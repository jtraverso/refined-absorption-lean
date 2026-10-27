# Fuentes y comprobaciones de la tercera revisión

Consulta: 27 de octubre de 2026. Las fuentes se usan para atribución, alcance y lectura de enunciados. No sustituyen la verificación formal. Se conservan aquí los localizadores y las conclusiones de esa consulta previa; los PDFs de terceros y sus extracciones no se redistribuyen en este paquete.

| Cuestión | Fuente primaria y ubicación | Resultado de la consulta |
|---|---|---|
| Familia refinada | [Delcourt–Postle, arXiv:2402.17855v1](https://arxiv.org/html/2402.17855v1), Definición 1.9 | Incidencia por arista acotada y tamaño de cada miembro acotado en vértices y aristas. El ejemplo de una arista por raíz satisface las dos condiciones. |
| Intersección en aristas y encaje global | [Erdős meets Nash-Williams](https://arxiv.org/html/2507.23624v1), Apéndice B, Definiciones B.1–B.2, Lema B.3 y su prueba | La condición sobre una arista nueva exige que su parte antigua esté contenida en una arista de J. La definición de encaje usa una inyección global. Se siguió la remisión del survey hasta la prueba. |
| Edición del survey | [SIAM, DOI 10.1137/25M1805977](https://epubs.siam.org/doi/10.1137/25M1805977), ICM 2026, vol. 6, pp. 212–231, Definiciones 3.6–3.7 y Lema 3.8 | Se verificaron identidad bibliográfica y persistencia del enunciado global. No se afirma igualdad total entre edición publicada y arXiv. |
| Cota para conjuntos peligrosos | [PDF de arXiv:2402.17855v1](https://arxiv.org/pdf/2402.17855v1), p. 38, §6.3, párrafo sobre la segunda modificación para Teorema 6.3, antes de Observación 6.5 | Se comprobó visualmente el exponente q−r+1 y que cuenta conjuntos por una arista fija de J. La reserva tiene el conjunto ambiente completo de vértices. No se atribuye número de ecuación inexistente. |
| Existencia de diseños | [Keevash](https://arxiv.org/abs/1401.3665), primera versión 2014, v4 de 2024 | Antecedente de la prueba de la conjetura de existencia. |
| Absorción iterativa | [Glock–Kühn–Lo–Osthus](https://arxiv.org/abs/1611.06827); [registro institucional de la publicación](https://research.birmingham.ac.uk/en/publications/the-existence-of-designs-via-iterative-absorption-hypergraph-f-de/) | Memoirs AMS 284, n.º 1406 (2023), DOI 10.1090/memo/1406. Se añade como antecedente, no como nueva dependencia lógica. |
| Exceso polinómico de colores | [Molloy–Reed, Near-optimal list colorings](https://onlinelibrary.wiley.com/doi/abs/10.1002/1098-2418%28200010/12%2917%3A3/4%3C376%3A%3AAID-RSA10%3E3.0.CO%3B2-0), Random Structures & Algorithms 17(3–4) (2000), 376–402 | El antecedente cubre hipergrafos uniformes lineales, incluso listas. La nota no identifica su contrato con el resultado de cogrados generales usado aquí ni reivindica novedad del exponente. |
| Palomar | [About Palomar](https://palomar-registry.org/about) | Se define su función de registro y se separan preflight, envío y registro final. El estado concreto se toma de recibos locales fechados, no del sitio en vivo. |
| Kernels adicionales | [NanoDa](https://github.com/ammkrn/nanoda_lib), [con-ron](https://github.com/leanprover/con-ron) | Referencias de los verificadores. Las identidades binarias del preflight están en su informe mecánico archivado; no se sustituye esa evidencia por la versión actual de los repositorios. |
| Software exploratorio | [Certo](https://github.com/jtraverso/certo-math), [Jacobian](https://github.com/morluto/jacobian) | Repositorios comprobados. No se dispone de registro de la versión exacta utilizada en la exploración original. Esa limitación se declara y no afecta a las dependencias lógicas fijadas. |

## Correspondencia con Lean

- `RefinedAbsorption/GeneralEmbedding/Defs.lean`: `IsCRefinedFamily`, `IsCBounded` e `IsEdgeIntersecting`. El primero registra la incidencia por arista; las hipótesis de tamaño del sistema implican el tamaño acotado de las raíces. El predicado de intersección exige una arista de la raíz, condición más fuerte que elegir cualquier arista de J; el testigo la satisface.
- `RefinedAbsorption/FaithfulSurvey2025/Embedding.lean`: `GeneralEmbeddingLemmaLiteral`, `not_generalEmbeddingLemmaLiteral` y `generalEmbedding_piecewise`. No hay namespace adicional `Literal`: es una sección.
- `RefinedAbsorption/Extensions/Intersection.lean`: `steiner_intersection_prescribed` elige las constantes antes de cuantificar sobre orden, sistema y subfamilia. No se modifica su tipo ni su prueba.
- `RefinedAbsorption/Upstream/PippengerSpencer/Polynomial.lean`: resultado `Pseudorandom.chromatic_index_polynomial`, incorporado desde el commit `b19273396d369332fb489fe07e61e27c9e7f9233`. Se numera la entrada expositiva existente como Teorema 6.1.
- `publication/assembly/VALIDATION.json`: evidencia congelada de 360 consultas de axiomas. La auditoría documental verifica los hashes de las fuentes, no vuelve a ejecutar Lean.
- `publication/palomar/OFFICIAL_PREFLIGHT.json` y `SUBMISSION_STATUS.json`: preflight exitoso y estado histórico `verifying`, ambos del 27 de octubre de 2026. Ninguno acredita por sí solo registro final.

## Búsqueda acotada sobre intersecciones

Se buscaron trabajos sobre intersecciones de sistemas de Steiner generales y absorción mediante consultas como «Steiner systems exact intersections general designs absorption intersection spectrum». Aparecieron antecedentes clásicos y resultados de parámetros particulares. No se estableció una comparación completa de prioridad para la Proposición 5.3. Por ello no se añade una reivindicación de novedad ni se afirma que no exista literatura pertinente. Se conservan las referencias de Lindner–Rosa y la descripción de estas proposiciones como consecuencias reutilizables del desarrollo formal.
