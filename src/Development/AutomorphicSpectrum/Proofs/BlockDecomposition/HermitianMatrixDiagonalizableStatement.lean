module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMatrixDiagonalizable
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

theorem _root_.GlobalTheory.T.hermitian_matrix_diagonalizable : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (n : ℕ) (h : Matrix (Fin n) (Fin n) R), cT σ h = h → ∃ (g g' : Matrix (Fin n) (Fin n) R) (d : Fin n → R), g * g' = 1 ∧ g' * g = 1 ∧ (∀ i, σ (d i) = d i) ∧ cT σ g * h * g = Matrix.diagonal d := by
  first | exact @GlobalTheory.CompanionTheory.HermDiag.herm_diag | exact GlobalTheory.CompanionTheory.HermDiag.herm_diag | (intros; apply GlobalTheory.CompanionTheory.HermDiag.herm_diag <;> assumption)
