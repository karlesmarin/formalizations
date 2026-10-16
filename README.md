# atiyah-l2-lean

Formalizaciones en Lean 4 de la investigación atiyah-l2: campos libres, altura de inversión y el problema 3XX en C[F₃].
- Autor: Carles Marín, con Claude como asistente.
- Lean v4.35.0. Mathlib fijado en `f0b4c815` (ver `lakefile.lean`).
- Solo se importan módulos de Mathlib, nunca `import Mathlib` entero.
- Sin `sorry`; los únicos axiomas son los estándar (`propext`, `Classical.choice`, `Quot.sound`).

```
lake exe cache get
lake build
```

## Módulos

| Módulo | Contenido |
|---|---|
| `DGHStrat` | Estratificación de Dubrovin–Gräter–Hanke `D : Ordinal → Set R` (Jakobs 2019, Def. 1.1.4) |
| `DGHLex` | Orden de Dershowitz–Manna = orden de Jakobs (lexicográfico desde el mayor) |
| `DGHHessenberg` | Orden de Jakobs leído por la suma natural de Hessenberg |
| `DGHAbsorb` | Sumas iteradas, absorción de una capa de inversas, identidad de Hua |
| `DGHFinite` | Estratos finitos de `D M`; `D M ω` como subanillo |
| `DGHEps0` | κ ≤ ε₀: `D M ε₀` es cerrado por sumas, productos e inversas |
| `Continuantes` | Continuante de Euler no conmutativo; a⁻¹ + r + b⁻¹ = a⁻¹ K(a,r,b) b⁻¹ |
| `FqLower` | Núcleo combinatorio de la cota inferior κ(F_q(x)) = ω² |
| `FreeLocusLinAlg` | Ingredientes de álgebra lineal de la obstrucción por loci libres |
| `LociLibresCert` | Corrección (una dirección) del certificado de loci libres |
| `T151Residuos` | Mecanismo de residuo y dirección de traza (3XX) |
| `T152Identidades` | Cadena del residuo degenerado (3XX) |
| `T155Identidades` | Fórmula de bloques de det, extractores de traza y de det, descomposición de Fox |
| `T158Identidades` | Arco exacto U² = t^{k+1}I, evaluación escalar, dos ejes, característica p |

## Estado
Repositorio privado mientras los resultados no estén publicados. El depósito en Zenodo lo decide Carles.
