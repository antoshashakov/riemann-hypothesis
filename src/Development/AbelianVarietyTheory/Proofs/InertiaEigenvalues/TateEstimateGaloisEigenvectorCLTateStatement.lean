module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateEstimateGaloisEigenvectorCLTate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tate_estimate_galois_eigenvector_cLTate : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l) (u : ℚ_[l]) (y : ℂ_[l]) (z : Om l) (N : ℕ) (e δ : ℝ), Per.σC γ y = algebraMap ℚ_[l] ℂ_[l] u * y → ‖u‖ = 1 → (γ ^ N) z = z → ‖y - (z : ℂ_[l])‖ ≤ e → ‖∑ i ∈ Finset.range N, (γ ^ i) (γ z - algebraMap ℚ_[l] (Om l) u * z)‖ ≤ δ * ‖γ z - algebraMap ℚ_[l] (Om l) u * z‖ → 0 ≤ δ → ‖u ^ N - 1‖ * ‖y‖ ≤ max (‖u - 1‖ * e) (δ * e) := by
  first | exact @GlobalTheory.InertiaEigenvalues.tate_eigenvector_estimate | exact GlobalTheory.InertiaEigenvalues.tate_eigenvector_estimate | (intros; apply GlobalTheory.InertiaEigenvalues.tate_eigenvector_estimate <;> assumption)
