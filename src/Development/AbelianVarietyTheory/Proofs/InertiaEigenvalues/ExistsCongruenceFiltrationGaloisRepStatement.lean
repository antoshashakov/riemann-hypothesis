module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCongruenceFiltrationGaloisRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_congruenceFiltration_galoisRep : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]), (∀ i j, Continuous fun g => (ρ g : Matrix n n ℚ_[l]) i j) → ∃ N : ℕ → Subgroup ↥(GK K), (∀ k g, g ∈ N k ↔ ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) ∧ Antitone N ∧ (∀ k, IsOpen (N k : Set ↥(GK K))) ∧ (∀ k g, g ∈ N k → g ^ l ∈ N (k + 1)) ∧ (∀ k g, g ∈ N 0 → g ^ l ∈ N (k + 1) → g ∈ N k) ∧ ∀ g, (∀ k, g ∈ N k) → ρ g = 1 := by
  first | exact @GlobalTheory.congrFiltration | exact GlobalTheory.congrFiltration | (intros; apply GlobalTheory.congrFiltration <;> assumption)
