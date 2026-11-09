/-
Usage example of the reusable layer, area AlgebraicGeometry, with the minimal import of that area:
the same code a user pastes into a file of their own project (README, section "Reusable layer").
-/
import Formalizations.Reusable.AlgebraicGeometry

open Formalizations.Reusable

/-- Cotes: the harmonic-mean point lies on the polar of `p`. -/
example (f : MvPolynomial (Fin 2) ℝ) (p v : Fin 2 → ℝ) (hp : MvPolynomial.eval p f ≠ 0)
    (hsplit : (MvPolynomial.aeval (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X)
      f).roots.card = (MvPolynomial.aeval
        (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X) f).natDegree)
    (hd : 1 ≤ (MvPolynomial.aeval
        (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X) f).natDegree)
    (hH : ((MvPolynomial.aeval (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X)
      f).roots.map (fun r => r⁻¹)).sum ≠ 0) :
    let g := MvPolynomial.aeval (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X) f
    ∑ i, MvPolynomial.eval p (MvPolynomial.pderiv i f) *
        ((g.natDegree : ℝ) / (g.roots.map (fun r => r⁻¹)).sum * v i)
      = -(g.natDegree : ℝ) * MvPolynomial.eval p f :=
  cotes_harmonic_mean_polar f p v hp _ rfl hsplit hd hH
