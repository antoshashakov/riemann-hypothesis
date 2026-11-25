module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMaximalAbelianHermitian
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix Topology Filter

theorem _root_.GlobalTheory.T.exists_maximal_abelian_hermitian : ∀ {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)), ∃ 𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), 𝔞 ≤ 𝔤 ∧ (∀ A ∈ 𝔞, Aᴴ = A) ∧ (∀ A ∈ 𝔞, ∀ B ∈ 𝔞, A * B = B * A) ∧ ∀ Y ∈ 𝔤, Yᴴ = Y → (∀ A ∈ 𝔞, Y * A = A * Y) → Y ∈ 𝔞 := by
  first | exact @GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace | exact GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace | (intros; apply GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace <;> assumption)
