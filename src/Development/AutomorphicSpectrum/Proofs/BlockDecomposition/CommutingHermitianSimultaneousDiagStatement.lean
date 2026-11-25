module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingHermitianSimultaneousDiag
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix Topology Filter

theorem _root_.GlobalTheory.T.commuting_hermitian_simultaneous_diag : ∀ {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℂ)), (∀ A ∈ S, Aᴴ = A) → (∀ A ∈ S, ∀ B ∈ S, A * B = B * A) → ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A ∈ S, (Uᴴ * A * U).IsDiag := by
  first | exact @GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag | exact GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag | (intros; apply GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag <;> assumption)
