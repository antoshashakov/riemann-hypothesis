module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerColumnRecursion
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

theorem _root_.GlobalTheory.T.whittaker_column_recursion : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ), j < d →
    (patSet (K := K) (colGe d j)).ncard = Fintype.card K ^ j * (patSet (K := K) (colGe d (j + 1))).ncard →
    (∀ x : Fin j → K, (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) = if x = 0 then (Fintype.card K : ℂ) ^ j else 0) →
    wh (colGe d (j + 1)) (colGeE K d (j + 1)) ψ₀ χ = ∑ r : Fin j → K, wh (colGe d j) (colGeR K d j r) ψ₀ χ := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.wh_colGe_succ_eq_sum | exact GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.wh_colGe_succ_eq_sum | (intros; apply GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.wh_colGe_succ_eq_sum <;> assumption)
