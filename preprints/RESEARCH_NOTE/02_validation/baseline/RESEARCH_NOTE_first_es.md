---
title: 'Formalización de la absorción refinada: interfaces de prueba y consecuencias'
author: 'Juan Pablo Traverso Gianini'
date: '27 de octubre de 2026'
---

**Research note — prepublicación 1.0, 27 de octubre de 2026.**

**Borrador editorial.** La fuente formal está congelada; quedan pendientes la reserva del DOI y la publicación pública.

© 2026 Juan Pablo Traverso Gianini. Licencia [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

## Resumen

Describimos una formalización en Lean de resultados principales del artículo de absorción refinada de Delcourt y Postle y de la survey de Postle, centrada en las interfaces entre sus argumentos. Tres casos explican el emparejamiento con reserva, la evitación en descomposiciones compatibles y la deducción de absorbedores compatibles. Distinguimos la independencia de un conjunto ambiente de vértices antiguos de la independencia del soporte de sus aristas, y damos una obstrucción finita a la conclusión de encaje global de la survey, junto con la variante por piezas demostrada. Un teorema de completación produce después intersecciones dispersas prescritas, encajes como intersecciones exactas e intervalos iniciales de intersección de orden polinómico. Finalmente, resultados externos demostrados de coloreo y Nash–Williams dan cotas de exceso polinómico para clases paralelas parciales y calendarios de descomposiciones en triángulos. Presentamos deducciones verificadas y aclaraciones de interfaces; no reivindicamos prioridad histórica para cada consecuencia. El complemento de formalización y reproducibilidad identifica las declaraciones, versiones de las fuentes, dependencias fijadas y evidencia de compilación.

**Palabras clave:** absorción refinada; diseños; formalización; sistemas de Steiner; intersecciones; coloreo de aristas de hipergrafos.

## 1. Fuentes y propósito

Una demostración por absorción suele leerse en dos escalas. En la escala mayor, una reserva dispersa y un absorbedor convierten una descomposición aproximada en una exacta. En la menor, los argumentos sucesivos deben entregarse el objeto adecuado: una familia con una cota local de carga, un packing que evite una familia prescrita o un encaje con la inyectividad precisa que necesita el argumento siguiente. La formalización explicita esas interfaces menores.

Las fuentes son *Refined Absorption: A New Proof of the Existence Conjecture*, de Delcourt y Postle [1], y la survey de Postle [2]. Usamos arXiv:2402.17855v1 para el artículo y arXiv:2510.19978v1 como base de los enunciados de la survey. Esta última apareció en las actas del ICM 2026. El DOI publicado identifica la obra; la versión de arXiv precisa el texto con el que comenzó el desarrollo. Las definiciones de encaje y el lema pertinentes también se contrastaron con la edición publicada.

La biblioteca contiene los resultados de omni-absorbedores refinados y refinadores de [1, Teoremas 1.7 y 1.11], sus resultados de descomposición densa y compatibilidad, y el teorema de omni-absorbedores refinados eficientes de la survey. El resultado de existencia de diseños cubre cada índice fijo $\lambda\ge1$ para $q>r\ge2$, con un conjunto de bloques sin repeticiones, en todos los órdenes admisibles suficientemente grandes. Son resultados de los autores citados. Remitimos a sus teoremas principales sin reproducir todo el desarrollo de absorción.

El propósito de esta nota es más acotado. Las Secciones 3 y 4 explican puntos en que una interfaz requiere cuidado, incluida la distinción entre el encaje global de la survey y un encaje por piezas. Las Secciones 5 y 6 desarrollan algunas consecuencias de las interfaces establecidas. El argumento de completación resulta especialmente útil: convierte la compatibilidad con un packing en control exacto de los bloques comunes.

Esta es una research note sobre formalización y sus consecuencias matemáticas, sin reivindicar una nueva teoría de existencia. Los problemas de intersección de sistemas triples de Steiner son clásicos; el trabajo de Lindner y Rosa [10], con su fe de erratas [11], precede a estas deducciones. No afirmamos obtener el espectro completo de intersecciones ni prioridad histórica para cada corolario de parámetros generales. El valor del desarrollo formal reside en poder seguir las hipótesis, los objetos intermedios y las aplicaciones finales a través de una colección de pruebas comprobadas.

## 2. Un marco mínimo

Todos los objetos son finitos. Fijamos enteros $q>r\ge1$, salvo cuando se indica una cota inferior más fuerte para $r$. Un $r$-grafo es un conjunto de aristas de $r$ elementos. Escribimos $K_V^r$ para el $r$-grafo completo sobre $V$. Para un $r$-grafo $G$ y un conjunto $S$ de tamaño $(r-1)$, sea
$$
d_G(S)=|\{e\in G:S\subseteq e\}|.
$$
El mínimo y el máximo de estos grados se denotan por $\delta_{r-1}(G)$ y $\Delta_{r-1}(G)$. Para grafos ordinarios son los grados usuales de los vértices.

Una $K_q^r$-descomposición de $G$ es una familia de conjuntos de $q$ elementos cuyos subconjuntos de tamaño $r$ particionan $G$. Un packing cubre cada arista a lo sumo una vez. Un sistema parcial de Steiner es una familia de conjuntos de $q$ elementos en la que cada conjunto de $r$ elementos aparece a lo sumo una vez; un sistema de Steiner cubre cada conjunto de $r$ elementos exactamente una vez. Para una familia de bloques $P$, escribimos
$$
H(P)=\bigcup_{B\in P}\binom Br.
\tag{2.1}
$$
Así, $H(P)$ es un $r$-grafo, mientras que $P$ es una familia de conjuntos de $q$ elementos. Distinguir ambos niveles será importante en la hipótesis de dispersión de la Sección 5.

La condición usual de divisibilidad para un diseño simple de índice $\lambda$ es
$$
\binom{q-i}{r-i}\ \bigm|\ \lambda\binom{n-i}{r-i}
\qquad(0\le i<r).
\tag{2.2}
$$
Llamamos admisible a $n$ cuando (2.2) se cumple con $\lambda=1$. Para un grafo ambiente general $G$, la divisibilidad exige que $\binom{q-i}{r-i}$ divida el número de aristas de $G$ que contienen cada conjunto de tamaño $i$. Restar las aristas de una descomposición conserva estas condiciones.

El resultado de descomposición densa es [1, Teorema 6.1]. Su forma compatible, [1, Teorema 6.3], afirma que, para $q>r\ge1$ fijos, un grafo ambiente divisible suficientemente grande con grado mínimo de conjuntos de tamaño $(r-1)$ al menos $(1-\varepsilon)n$ admite una descomposición compatible con cualquier packing prescrito $Q_1$: la salida $Q_2$ satisface
$$
|B_1\cap B_2|\le r
\qquad(B_1\in Q_1,\ B_2\in Q_2).
\tag{2.3}
$$
La constante positiva $\varepsilon$ y el umbral de orden dependen sólo de $q,r$. En particular, el packing prescrito no tiene que ser disperso. La ecuación (2.3) excluye un bloque común porque $q>r$.

## 3. Tres interfaces de prueba

### 3.1. Emparejamiento con reserva y conjuntos de prueba

El enunciado de emparejamiento con reserva es [1, Teorema 2.8], cuyos antecedentes de emparejamiento están en [3]. Fijamos $s\ge2$ y $0<\beta<1$, y escribimos $s$ para la uniformidad de su multi-hipergrafo auxiliar; ese parámetro se llama $r$ en el teorema citado. Las aristas tienen etiquetas, de modo que distintas copias pueden tener los mismos extremos. La parte principal $G_1$ tiene grados a lo sumo $D$ y grados al menos $D(1-D^{-\beta})$ en un conjunto designado $A$. Una segunda parte $G_2$ proporciona muchas opciones por cada punto de $A$, con exactamente uno de esos puntos por arista. Sus otros vértices tienen grado a lo sumo $D$, y los dos conjuntos de vértices se intersectan exactamente en $A$. Los cogrados están acotados por $D^{1-\beta}$.

La conclusión es un emparejamiento que cubre $A$. La casi regularidad se exige en $A$ dentro de la parte principal; no es una hipótesis sobre cada vértice de todo el multi-hipergrafo. El resultado formal conserva las copias etiquetadas y el contrato completo de la reserva.

El paso del nibble a la reserva es el siguiente. Retenemos
$$
t=\lceil D^{1-\alpha}\rceil
$$
opciones de reserva por cada raíz $a\in A$, donde $\alpha>0$ se elegirá más adelante. Para un vértice de reserva $b\notin A$, sea $w_b(a)$ el número de opciones retenidas que pasan por $a$ y $b$. Las cotas de grados y cogrados dan
$$
\sum_{a\in A}w_b(a)\le D,
\qquad
0\le w_b(a)\le\lfloor D^{1-\beta}\rfloor.
\tag{3.1}
$$
Si el nibble deja sin cubrir $U\subseteq A$, la carga todavía visible en $b$ es $\sum_{a\in U}w_b(a)$. Una cota sobre $|U|$ por sí sola no controlaría esa suma: las raíces sin cubrir podrían concentrarse en las opciones que utilizan un mismo vértice.

Usamos los conjuntos de nivel
$$
T_{b,j}=\{a\in A:w_b(a)\ge j\}.
$$
El nibble se aplica con conjuntos de prueba tomados de esos niveles. Sus tamaños y el número de conjuntos que pasan por un vértice tienen cotas polinómicas en $D$. Esta interfaz no impone una cota sobre el número total de conjuntos de prueba ni sobre el número total de aristas del multi-hipergrafo ambiente. Los niveles pequeños se controlan por su tamaño; el nibble controla los mayores.

El nibble local proporciona una constante $c>0$. Ponemos $D_0=\lfloor D\rfloor$. Las cotas resultantes, escritas en la forma común
$$
|U\cap T_{b,j}|
\le D_0^{-c}|T_{b,j}|+D_0^{\beta/2},
$$
se pueden sumar sobre los niveles enteros. En efecto, contar cada raíz una vez por cada nivel inferior a su peso da
$$
\begin{aligned}
\sum_{a\in U}w_b(a)
&=\sum_{j=1}^{\lfloor D^{1-\beta}\rfloor}|U\cap T_{b,j}|\\
&\le D_0^{-c}D+
 \lfloor D^{1-\beta}\rfloor D_0^{\beta/2}.
\end{aligned}
\tag{3.2}
$$
Esta es la estimación de carga que necesita el argumento de reserva. Explica por qué sirve una interfaz con conjuntos de prueba locales aun cuando ya se dispone de una estimación global del residuo.

Las elecciones numéricas tienen un propósito sencillo. Ponemos
$$
c'=\min\{c,\beta/2\},\qquad
\alpha=c'/8,\qquad p=D^\alpha/t.
\tag{3.3}
$$
Seleccionamos opciones de reserva independientemente con probabilidad $p$. Los eventos malos son que una raíz no reciba ninguna opción o que se seleccionen dos opciones que se intersectan. Sus probabilidades se acotan por $e^{-D^\alpha}$ y $p^2$, respectivamente. La ecuación (3.2) acota los grados de reserva pertinentes por $O(D^{1-c'})$ y con ello controla las dependencias locales. Para los eventos de colisión, el producto resultante es de orden $D^{3\alpha-c'}$, que tiende a cero por (3.3); el término exponencial también domina la cota polinómica de dependencias. El lema local proporciona entonces un emparejamiento que cubre las raíces pendientes.

Su unión con el emparejamiento del nibble sigue siendo un emparejamiento. Los vértices de reserva fuera de $A$ no pertenecen al conjunto principal de vértices, y sus raíces en $U$ estaban sin cubrir. Esta última observación explica la necesidad de conservar la intersección exacta de conjuntos de vértices en la interfaz. Los pisos, techos y desigualdades válidas a partir de un umbral se comprueban en la prueba formal; no alteran esta división del argumento.

### 3.2. La evitación debe conservarse al absorber

Para [1, Teorema 6.3], fijamos un packing $Q_1$ y llamamos $\mathcal D$ a la familia de conjuntos peligrosos de tamaño $q$: los que intersectan un bloque de $Q_1$ en al menos $r+1$ vértices. El lema formal de conteo da, a través de cada $r$-arista fija $e$,
$$
|\{Q\in\mathcal D:e\subseteq Q\}|
\le 2^r q\,n^{q-r-1}.
\tag{3.4}
$$
Este exponente es una unidad menor que el orden $n^{q-r}$ de los cliques disponibles a través de una arista.

Para ver esa ganancia, sea $P\in Q_1$ un testigo de que $Q$ es peligroso y pongamos $A=e\cap P$. Elegimos $B\subseteq(Q\cap P)\setminus e$ de modo que $|A\cup B|=r$, y después un punto adicional $y\in(Q\cap P)\setminus(A\cup B)$. El conjunto de tamaño $r$ dado por $A\cup B$ determina a lo sumo un bloque $P$, porque $Q_1$ es un packing. Hay a lo sumo $2^r$ elecciones de $A$, a lo sumo $n^{r-|A|}$ de $B$ y a lo sumo $q$ de $y$ una vez determinado $P$. Los puntos restantes de $Q$ contribuyen a lo sumo $n^{q-2r+|A|-1}$. Si el conjunto forzado es demasiado grande, no hay tal $Q$. En caso contrario, los exponentes suman $q-r-1$, lo que da (3.4).

El último párrafo de la discusión pertinente de [1, Sección 6.3] imprime el orden más débil $n^{q-r+1}$. Una cota superior más fuerte no contradice esa cota superior. El problema para la demostración es que la estimación más débil no aporta la ganancia usada al eliminar los cliques peligrosos. La ecuación (3.4) sí la aporta.

La evitación debe imponerse en dos lugares. Primero, el catálogo de bloques disponibles para el omni-absorbedor debe ser seguro frente a $Q_1$. Segundo, el nibble y su completación con reserva deben utilizar bloques seguros. Restringir solamente el packing aproximado final dejaría sin controlar la descomposición seleccionada por el absorbedor.

Una vez elegido el absorbedor seguro, se lo retira junto con la reserva del grafo de trabajo. El refuerzo de regularidad proporciona la familia de cliques para la cobertura principal. El presupuesto de eliminación de (3.4) es suficientemente pequeño para conservar la oferta requerida, y el nibble seguro deja un residuo divisible en la reserva. El absorbedor trata después ese residuo utilizando su catálogo, ya seguro. Las dos familias de bloques de la unión final satisfacen (2.3), por lo que también la satisface la unión. La biblioteca trata $r=1$ por separado; la discusión anterior del nibble corresponde a $r\ge2$.

### 3.3. Absorbedores compatibles a partir de descomposiciones compatibles

La deducción de [1, Teorema 6.2] puede expresarse sin otra construcción de absorción. Sea $L$ el $r$-grafo divisible dado sobre su conjunto de vértices antiguos. Elegimos un conjunto admisible $U$ que contenga todos los vértices antiguos, y después un conjunto admisible mucho mayor $W\supseteq U$. Ponemos
$$
A_0=K_W^r\setminus K_U^r.
\tag{3.5}
$$
Los dos grafos completos son divisibles, por lo que $A_0$ también lo es. Tomar $W$ suficientemente grande respecto de $U$ hace que $A_0$, y también $A_0\cup L$, tengan la densidad requerida por los dos resultados de descomposición.

Aplicamos [1, Teorema 6.1] para obtener una descomposición $Q_1$ de $A_0$. Es un packing en $A_0\cup L$. Aplicamos [1, Teorema 6.3] a ese grafo mayor con packing prescrito $Q_1$, y obtenemos una descomposición $Q_2$ que satisface (2.3). Así, $A_0$ y $A_0\cup L$ tienen descomposiciones compatibles.

Toda arista de $A_0$ usa un vértice fuera de $U$. Por tanto, el conjunto completo de vértices antiguos es independiente en $A_0$. Reetiquetar los vértices añadidos fijando los antiguos da el absorbedor buscado. La construcción separa tres obligaciones: divisibilidad por sustracción, densidad por ampliación y compatibilidad por el teorema del packing prescrito. Además, explicita la condición sobre vértices ambientes que discutimos a continuación.

## 4. Dos distinciones de fidelidad

### 4.1. Vértices antiguos y soporte de aristas

Una representación por conjuntos de aristas recuerda los vértices que aparecen en ellas. Un hipergrafo con conjunto ambiente explícito también puede tener vértices aislados. Estas convenciones son intercambiables en muchos enunciados de conteo de aristas, pero la frase «los vértices antiguos son independientes» exige identificar el conjunto antiguo.

El predicado de absorbedor conservado usa el soporte de $L$. La interfaz añadida para el Teorema 6.2 del artículo también afirma que ninguna arista del absorbedor está completamente contenida en el conjunto ambiente antiguo, incluidas las etiquetas aisladas. La construcción (3.5) lo demuestra directamente porque todos los vértices antiguos se incluyeron en $U$. Se permiten aristas mixtas que contengan vértices antiguos y nuevos.

Se conserva el resultado anterior. La cláusula añadida registra información que ya proporciona la misma construcción; no se presenta como un nuevo teorema de existencia de absorbedores. Es una distinción útil entre fortalecer la interfaz pública y cambiar la prueba subyacente.

### 4.2. Encajes globales y por piezas

La Definición 3.7 de la survey pide una sola aplicación inyectiva sobre la unión de un sistema de supergrafos, que fije los vértices antiguos del grafo ambiente. Su Lema 3.8 obtiene una conclusión de ese tipo a partir de conteos locales de encajes y una hipótesis de dispersión. La formalización separa la inyectividad global, la inyectividad en cada pieza y la distinción de las imágenes de aristas nuevas.

Hay una obstrucción finita a la conclusión global. Tomamos $n$ par y un emparejamiento perfecto $J$ que abarque todos los vértices de $K_n$. Por cada arista $H$ del emparejamiento, añadimos un vértice nuevo privado para formar un triángulo $W_H$. Con los parámetros de la survey
$$
r=2,\qquad C=3,\qquad \gamma=1/2,
\tag{4.1}
$$
cada pieza tiene $n-2\ge n/2$ encajes con raíces fijas para $n\ge4$. Las otras aristas del emparejamiento no obstruyen esos encajes: las dos aristas nuevas del triángulo tocan los extremos de $H$. Las condiciones de refinamiento y tamaño acotado se cumplen con $C=3$. Además, $\Delta(J)=1$, por lo que la desigualdad de dispersión $\Delta(J)\le n/C'$ se cumple para cualquier constante propuesta $C'$ cuando $n$ es suficientemente grande.

Sin embargo, una inyección global que fije los $n$ vértices antiguos no tiene una imagen disponible ni siquiera para un vértice nuevo privado. Las piezas cubren todos los vértices antiguos, por lo que la obstrucción también se aplica si el dominio global se define usando sólo los vértices antiguos que aparecen en las piezas indexadas. No depende de una convención sobre vértices antiguos no utilizados.

La survey remite a [4, Apéndice B] para la prueba. Ese apéndice está disponible e incluye una demostración; también escribe una inyección global en su definición. El problema está en la conclusión, no en la ausencia de una referencia. Su argumento de extensión controla las cargas locales y las colisiones de aristas nuevas. Esos controles deben distinguirse de la inyectividad sobre todos los vértices de la unión.

La biblioteca demuestra una variante por piezas con imágenes distintas de aristas nuevas. Un vértice nuevo de una pieza puede coincidir entonces con un vértice de otra, siempre que se cumplan las condiciones del encaje individual y de las aristas. La inyectividad global prohibiría esas coincidencias. La variante demostrada y la negación formal de la afirmación global tienen declaraciones separadas. Ninguna se describe como una prueba de la otra.

## 5. Completación e intersecciones exactas

La interfaz de descomposición compatible da un argumento breve de completación. Lo enunciamos con su condición completa de dispersión, porque es fácil interpretarla mal.

#### Teorema 5.1

Para $q>r\ge1$ fijos existen $\varepsilon>0$ y $n_0$ tales que lo siguiente se cumple para todo $n\ge n_0$ admisible. Sean $P,F$ sistemas parciales de Steiner sobre los mismos $n$ puntos. Si
$$
\Delta_{r-1}(H(P))\le\varepsilon n,
\tag{5.1}
$$
existe un sistema de Steiner $\mathcal S$ con
$$
P\subseteq\mathcal S,\qquad
\mathcal S\cap F=P\cap F.
\tag{5.2}
$$
Además, si $B\in F$ no tiene ninguna $r$-arista en $H(P)$, entonces
$$
|B\cap B'|\le r
\qquad(B'\in\mathcal S\setminus P).
\tag{5.3}
$$
No se impone dispersión a $F$.

*Demostración.* Retiramos $H(P)$ del $r$-grafo completo y llamamos $G$ al grafo residual. La familia $P$ descompone las aristas retiradas. Por tanto, la divisibilidad pasa de $K_n^r$ a $G$. La condición (5.1) retira a lo sumo $\varepsilon n$ extensiones de cada conjunto de tamaño $(r-1)$; eligiendo $\varepsilon$ suficientemente pequeño y $n_0$ suficientemente grande, $G$ cumple la hipótesis de grado mínimo del Teorema 6.3 del artículo.

Sea $F_0$ la familia de bloques de $F$ cuyos subconjuntos de tamaño $r$ están todos en $G$. Es un packing en $G$. Aplicamos [1, Teorema 6.3] con packing prescrito $F_0$ y llamamos $Q$ a la descomposición resultante de $G$. Ningún bloque de $Q$ pertenece a $F_0$: un bloque común tendría intersección de tamaño $q>r$ consigo mismo. Tampoco puede pertenecer a $Q$ un bloque de $F\setminus F_0$, porque alguna de sus $r$-aristas fue retirada.

Se sigue que $Q\cap F=\varnothing$. La familia $\mathcal S=P\cup Q$ descompone el $r$-grafo completo y satisface (5.2). Si $B$ cumple la condición adicional del teorema, entonces $B\in F_0$. La conclusión de cruce de [1, Teorema 6.3] da (5.3) para los bloques nuevos. $\square$

La dispersión de (5.1) mide las $r$-aristas cubiertas a través de un conjunto de tamaño $(r-1)$. No está enunciada como una cota de grados de puntos en la familia de bloques de tamaño $q$. La restricción que precede a (5.3) también importa: el teorema no hace esa afirmación de cruce para un bloque prohibido que use una arista ya cubierta por $P$.

#### Corolario 5.2

Para $q>r\ge1$ fijos se cumplen las siguientes afirmaciones.

(i) Todo sistema de Steiner $\mathcal S_1$ suficientemente grande y toda subfamilia $P\subseteq\mathcal S_1$ que satisfaga (5.1), para una constante fija adecuada $\varepsilon>0$, admiten un sistema de Steiner $\mathcal S_2$ con
$$
\mathcal S_1\cap\mathcal S_2=P.
\tag{5.4}
$$
Los bloques de $\mathcal S_1\setminus P$ y de $\mathcal S_2\setminus P$ tienen intersección de tamaño a lo sumo $r$.

(ii) Todo sistema parcial finito de Steiner aparece, tras una inyección de su conjunto de vértices, como la familia exacta de bloques comunes de dos sistemas de Steiner en todo orden admisible suficientemente grande.

*Demostración.* Para (i), usamos $F=\mathcal S_1$ en el Teorema 5.1. La existencia de $\mathcal S_1$ proporciona la admisibilidad. Un bloque de $\mathcal S_1\setminus P$ no tiene ninguna $r$-arista en $H(P)$, pues de lo contrario esa arista estaría en dos bloques de $\mathcal S_1$. Por tanto, la última afirmación se sigue de (5.3).

Para (ii), primero usamos el teorema usual de completación dispersa para extender un sistema parcial disperso a $\mathcal S_1$, y después aplicamos (i). Se pueden reducir las constantes de dispersión para que se apliquen ambos pasos. Para un sistema finito fijo sobre un conjunto de vértices de tamaño $u$, encajamos ese conjunto en otro mayor de tamaño $N$. Su $r$-grafo cubierto tiene grado máximo de conjuntos de tamaño $(r-1)$ a lo sumo $u$: cada extensión elige un punto del conjunto encajado. Por tanto, el grado es a lo sumo $\varepsilon N$ para todo $N$ suficientemente grande. Elegimos $N$ por encima de ambos umbrales de completación e imponemos admisibilidad. La construcción elige conjuntamente una inyección y los dos sistemas. $\square$

Tomar $P=\varnothing$ en el Teorema 5.1 proporciona un sistema de Steiner sin bloques comunes con un sistema parcial prescrito arbitrario, y con la cota de cruce (5.3). En particular, todo sistema de Steiner suficientemente grande tiene un compañero disjunto. «Disjuntos» se refiere a sus familias de bloques; ambos sistemas siguen cubriendo el mismo $r$-grafo completo.

#### Proposición 5.3

Para $q>r\ge1$ fijos existen $c>0$ y $n_0$ tales que, para todo $n\ge n_0$ admisible y todo entero $0\le k\le c n^r$, hay dos sistemas de Steiner sobre $n$ puntos con exactamente $k$ bloques comunes.

*Demostración.* Elegimos la constante de completación dispersa con $0<\varepsilon\le1$ y reservamos un conjunto de $u=\lfloor\varepsilon n\rfloor$ puntos. Un packing voraz sobre ese conjunto puede tener $k$ bloques siempre que
$$
2\binom qr^2 k\le\binom ur.
\tag{5.5}
$$
Para ver el margen disponible, cada bloque seleccionado descarta a lo sumo $\binom qr\binom{u-r}{q-r}$ bloques candidatos que contengan alguno de sus conjuntos de tamaño $r$. Contar todos los candidatos mediante $\binom uq$ da (5.5) como condición suficiente durante toda la construcción voraz.

El $r$-grafo cubierto por ese sistema parcial tiene grado máximo de conjuntos de tamaño $(r-1)$ a lo sumo $u$, por lo que se aplica la construcción de intersección exacta del Corolario 5.2. Para todo $n$ suficientemente grande,
$$
\binom{\lfloor\varepsilon n\rfloor}{r}
\ge\frac{(\varepsilon n/2)^r}{r!}.
$$
Por tanto, se puede tomar
$$
c=\frac{(\varepsilon/2)^r}{2r!\binom qr^2},
\tag{5.6}
$$
tras ampliar el umbral de orden. Los dos sistemas resultantes tienen en común precisamente los $k$ bloques elegidos. $\square$

La proposición elige ambos sistemas. No da el espectro completo ni prescribe $k$ bloques comunes con cualquier primer sistema fijado. Su función aquí es mostrar cómo una completación exacta y un packing de soporte pequeño producen un intervalo del mismo orden polinómico que el número total de bloques.

## 6. Cotas polinómicas para clases y calendarios

### 6.1. El resultado de coloreo

Una clase paralela parcial es una familia de bloques disjuntos en vértices dos a dos. Particionar una familia de bloques en esas clases equivale a colorear propiamente las aristas del hipergrafo cuyas aristas son los bloques.

El resultado cuantitativo usado aquí está demostrado en el desarrollo de Pippenger–Spencer fijado por commit, a través del teorema de emparejamiento seudoaleatorio de Ehard, Glock y Joos [6, Teorema 1.2]. El contexto clásico es [5]; no identificamos el contrato exacto siguiente con el teorema impreso en 1989.

Para $k\ge2$ fijo y $0<\delta<1$, existen $\gamma_0>0$ y $D_*$ tales que un hipergrafo $k$-uniforme de grado máximo a lo sumo $D\ge D_*$, cogrados a lo sumo $D^{1-\delta}$ y
$$
|E|\le\exp(D^{\gamma_0})
\tag{6.1}
$$
admite un coloreo propio de aristas con a lo sumo $D+D^{1-\gamma_0}$ colores. No hay hipótesis de grado mínimo. La cota sobre el número de aristas (6.1) forma parte del resultado de entrada y debe comprobarse.

### 6.2. Sistemas de Steiner

#### Teorema 6.2

Fijamos $q>r\ge2$. Existen $0<\gamma<1$ y $n_0$ tales que todo sistema de Steiner sobre $n\ge n_0$ puntos tiene una partición en clases paralelas parciales cuyo número es a lo sumo
$$
R+R^{1-\gamma},\qquad
R=\frac{\binom{n-1}{r-1}}{\binom{q-1}{r-1}}.
\tag{6.2}
$$
Tal sistema existe en todo orden admisible suficientemente grande. Toda partición en clases paralelas parciales requiere al menos $R$ clases.

*Demostración.* En el hipergrafo de bloques, que es $q$-uniforme, contar los conjuntos de tamaño $r$ que pasan por un punto y por un par da
$$
d(v)=R,\qquad
d(u,v)=R\frac{q-1}{n-1}\quad(u\ne v),\qquad
q|\mathcal S|=nR.
\tag{6.3}
$$
En particular, $R$ es un entero. Usamos el resultado de coloreo con $D=R$ y $\delta=1/(2(r-1))$. La fórmula binomial da $R\le(n-1)^{r-1}$, de donde $R^\delta\le\sqrt{n-1}$. Para $n$ grande también tenemos $q-1\le\sqrt{n-1}$. La identidad de cogrados de (6.3) da entonces $d(u,v)\le R^{1-\delta}$.

Para $n$ grande, todo par pertenece a un bloque, por lo que su cogrado es al menos uno. La ecuación (6.3) da $n-1\le R(q-1)$; como $R\ge1$, se sigue $n\le qR$. Junto con la identidad de conteo de bloques, esto da en particular la cota polinómica $|\mathcal S|\le qR^2$. Como $R$ tiende a infinito, esa cota implica (6.1) para el exponente $\gamma_0$ que proporciona efectivamente el resultado de coloreo. Aplicamos primero ese resultado y después ponemos $\gamma=\min\{\gamma_0,1/2\}$ para obtener (6.2). Los bloques de una clase de color son disjuntos en vértices. Los $R$ bloques que pasan por un punto fijo necesitan colores distintos, lo que prueba la cota inferior. Finalmente, combinamos la afirmación con el teorema de existencia de sistemas de Steiner ya establecido. $\square$

El error polinómico de (6.2) cuenta el exceso de clases. No da una cota para el número de vértices sin cubrir en cada clase individual, ni afirma una resolución en clases que abarquen todos los vértices. Los dos resultados formales separan el coloreo de todo sistema existente de la existencia en órdenes admisibles.

### 6.3. Calendarios Nash–Williams

El resultado de descomposición de grafos es el teorema de Nash–Williams para órdenes grandes de Delcourt y Postle [7]. Reutilizamos su resultado formal demostrado a través de las construcciones documentadas en [8,9]. Aquí no repetimos los argumentos de esos papers.

#### Teorema 6.3

Existen $0<\gamma<1$ y $n_0$ tales que todo grafo divisible en triángulos $G$ sobre $n\ge n_0$ vértices con
$$
3n\le4\delta(G)
\tag{6.4}
$$
tiene una descomposición en triángulos cuyo número de rondas es a lo sumo
$$
D+D^{1-\gamma},\qquad D=\Delta(G)/2,
\tag{6.5}
$$
con triángulos disjuntos en vértices en cada ronda. Todo calendario de ese tipo necesita al menos $D$ rondas.

*Demostración.* La divisibilidad en triángulos significa que todos los grados son pares y que $3$ divide el número de aristas. El resultado demostrado de Nash–Williams proporciona una descomposición en triángulos $T$ en el umbral exacto (6.4). Consideramos sus triángulos como un hipergrafo $3$-uniforme. Su grado en un vértice $v$ es $d_G(v)/2$, y un par tiene cogrado a lo sumo uno porque una arista de $G$ pertenece a un solo triángulo. Por tanto, su grado máximo es $D$.

No es necesario que $G$ sea casi regular: el resultado de coloreo sólo pide una cota superior de grados. Contar incidencias entre vértices y triángulos da $3|T|\le nD$, mientras que (6.4) da $D\ge3n/8$. En particular, $|T|\le3D^2$. Con $\delta=1/2$, las hipótesis de cogrados y número de aristas de la Sección 6.1 se cumplen para $n$ suficientemente grande. Coloreamos el hipergrafo de triángulos y reducimos el exponente de salida a $\gamma=\min\{\gamma_0,1/2\}$ como antes. Las clases de color dan las rondas requeridas. En un vértice de grado máximo, los $D$ triángulos incidentes deben aparecer en rondas distintas, lo que prueba la cota inferior. $\square$

Algunas etiquetas de color pueden no utilizarse; sólo se necesita la cota superior de rondas afirmada. Las rondas son familias de triángulos disjuntos en vértices, sin tener que ser factores de triángulos que abarquen todo el grafo. Las constantes y umbrales de ambas aplicaciones son existenciales y no se afirma que estén optimizados.

## 7. Alcance formal y reproducibilidad

Las pruebas están implementadas en Lean 4 [12] usando Mathlib [13]. El freeze formal usa Lean `4.35.0-rc3` y revisiones fijas de las dependencias. La campaña de Lake con directorio de salida del proyecto inicialmente vacío compiló 316 fuentes locales: 300 módulos de biblioteca, diez de comprobación y seis interfaces independientes de comparación. Las 360 consultas de axiomas de los resultados usan sólo `propext`, `Classical.choice` y `Quot.sound`, o ningún axioma. Los huecos deliberados de los Challenges de comparación son interfaces de enunciados; sus Solutions importan las declaraciones realmente demostradas.

El módulo raíz agregado importa toda la biblioteca local de pruebas. Se conservan los consumidores condicionales anteriores de coloreo y calendarios, mientras que el ensamblaje final proporciona ambos contratos externos mediante pruebas fijadas por commit. El complemento registra las declaraciones exactas y distingue esta evidencia local de las comprobaciones separadas de comparación y kernel de Palomar.

El alcance formalizado es selectivo. Incluye el resultado completo para cada índice fijo descrito en la Sección 1, pero no todas las aplicaciones del artículo o la survey; las afirmaciones generales de cintura alta quedan fuera del alcance establecido. El resultado de encaje por piezas es una variante, y la afirmación global literal tiene un contraejemplo formal separado. Estas precisiones forman parte de la exposición matemática.

El desarrollo se produjo bajo la dirección del autor con Aristotle y Codex. Aristotle contribuyó al desarrollo de pruebas y a la formalización. Codex contribuyó a la migración, el ensamblaje, las interfaces, la exposición y la auditoría interna. El autor es responsable de las afirmaciones matemáticas y editoriales. La revisión interna por agente no es una revisión independiente por pares humanos.

## Referencias

[1] M. Delcourt and L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture*, arXiv:2402.17855v1 (2024). <https://doi.org/10.48550/arXiv.2402.17855>.

[2] L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture and Its Applications to Extremal and Probabilistic Design Theory*, Proceedings of the International Congress of Mathematicians 2026, Volume 6, 212–231. <https://doi.org/10.1137/25M1805977>. Base de enunciados: arXiv:2510.19978v1 (2025), <https://doi.org/10.48550/arXiv.2510.19978>.

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
