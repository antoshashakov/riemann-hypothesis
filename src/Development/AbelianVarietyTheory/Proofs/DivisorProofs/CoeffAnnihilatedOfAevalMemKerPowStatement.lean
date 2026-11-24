module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAnnihilatedOfAevalMemKerPow
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.coeff_annihilated_of_aeval_mem_ker_pow : ∀ (d N : ℕ), ∃ K : ℕ, 0 < K ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (ε : B →ₐ[R] R) (y : Fin d → B) (D : Fin d → Derivation R B B), (∀ i, ε (y i) = 0) → (∀ i j, ε (D i (y j)) = if i = j then 1 else 0) → ∀ P : MvPolynomial (Fin d) R, (∀ α : Fin d →₀ ℕ, N ≤ α.degree → AddMonoidAlgebra.coeff P α = 0) → MvPolynomial.aeval y P ∈ RingHom.ker ε ^ N → ∀ α, (K : R) * AddMonoidAlgebra.coeff P α = 0 := by
  first | exact @GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero | exact GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero | (intros; apply GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero <;> assumption)
