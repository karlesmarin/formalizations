# 🔎 Coincidencias con `karlesmarin/formalizations`

Revisión del árbol `main` de `https://github.com/karlesmarin/formalizations`
el 19 de noviembre de 2026, antes de integrar la sesión Isabelle. La comparación
es de **enunciados y alcance**, no sólo de nombres de archivos.

| Resultado de la nota | Ya formalizado allí | Relación |
|---|---|---|
| Forma de Möbius de γ_Padé e inversa | [`GammaMobius.lean`](https://github.com/karlesmarin/formalizations/blob/main/Formalizations/Analysis/TransformerAttention/GammaMobius.lean), [`Pade.lean`](https://github.com/karlesmarin/formalizations/blob/main/Formalizations/Analysis/TransformerAttention/Pade.lean) | Coincidencia algebraica: se cita, no se vuelve a presentar como teorema nuevo. |
| Máxima entropía con restricción de log-distancia y ley de potencias | [`MaxEnt.lean`](https://github.com/karlesmarin/formalizations/blob/main/Formalizations/Analysis/TransformerAttention/MaxEnt.lean) | Comparte la familia exponencial, con un problema variacional más fuerte en Lean. Los lemas Isabelle aquí estudian derivadas, calibración, cuantiles y estabilidad. |
| Cota `H(p) ≤ log N` | [`EntropyBound.lean`](https://github.com/karlesmarin/formalizations/blob/main/Formalizations/Analysis/TransformerAttention/EntropyBound.lean) | Ya probada, incluso con igualdad caracterizada; no se reivindica como novedad. |
| Coeficiente `1/√12` de RoPE | [`CriticalExponents.lean`](https://github.com/karlesmarin/formalizations/blob/main/Formalizations/Analysis/TransformerAttention/CriticalExponents.lean) | Identidad numérica distinta del puente analítico Ci–RoPE. |
| Nulo instrumental, OLS, exposición afín y mezcla de perfiles | Sin sesión correspondiente en el árbol Isabelle/Lean revisado | Aquí se formalizan con hipótesis explícitas; no se afirma novedad matemática general. |
| Truncamiento, cota óptima de softmax por oscilación y salida vectorial | Sin sesión correspondiente en el árbol revisado | Los lemas Isabelle aportan versiones probabilísticas y normadas completas. |
| Integral de cosenos, Ci, error finito y puente condicional de scores RoPE a softmax | Sin sesión correspondiente en el árbol revisado | Usa `Exp_Log_Integral` de AFP como dependencia acreditada, y prueba el puente específico. |

Las pruebas estándar de análisis y probabilidad pueden tener otros antecedentes
fuera de este repositorio. **Formalizar una identidad no demuestra que prediga
un exponente en modelos entrenados.** La [integración en `formalizations`](https://github.com/karlesmarin/formalizations/tree/main/Isabelle/TransformerAttentionPartI)
conserva las teorías Isabelle como una sesión separada y enlaza los archivos
Lean existentes, sin copiarlos.
