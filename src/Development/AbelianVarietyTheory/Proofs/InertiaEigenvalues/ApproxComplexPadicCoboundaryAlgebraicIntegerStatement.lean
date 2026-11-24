module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproxComplexPadicCoboundaryAlgebraicInteger
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import GroundTheory.LocalFields.Interface

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.approx_complexPadic_coboundary_algebraic_integer : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Set (GQ l)) (x : ℂ_[l]) (a : GQ l → ℤ_[l]), (∀ σ ∈ S, ‖Formalism.Per.σC σ x - x - algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r) → ∃ (y : Om l) (b : GQ l → ℤ), (∀ σ ∈ S, ‖σ y - y - (b σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧ ∀ σ, (l : ℤ) ^ r ∣ b σ → (l : ℤ_[l]) ^ r ∣ a σ := by
  first | exact @GlobalTheory.PMon.Ram.approx_algebraic_integer | exact GlobalTheory.PMon.Ram.approx_algebraic_integer | (intros; apply GlobalTheory.PMon.Ram.approx_algebraic_integer <;> assumption)
