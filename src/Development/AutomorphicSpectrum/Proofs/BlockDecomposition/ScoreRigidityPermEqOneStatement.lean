module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScoreRigidityPermEqOne
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Finset GlobalTheory.CompanionTheory.CoefId

theorem _root_.GlobalTheory.T.score_rigidity_perm_eq_one : ∀ {n : ℕ} (lev : Fin n → ℕ), Monotone lev → ∀ L : Fin n → ℤ, StrictAnti L → (∀ a b, lev a = lev b → L a - L b = ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) → (∀ a b, lev a = lev b → score (tZero lev) a - ((a : ℕ) : ℤ) = score (tZero lev) b - ((b : ℕ) : ℤ)) → ∀ (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n × Fin n)), T ⊆ prs n → (∀ a, score T a = score (tZero lev) a + 2 * (L a - L (σ a))) → σ = 1 ∧ T = tZero lev := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.Unique.tournament_unique | exact GlobalTheory.CompanionTheory.CoefId.Unique.tournament_unique | (intros; apply GlobalTheory.CompanionTheory.CoefId.Unique.tournament_unique <;> assumption)
