module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRightConvolutionBoundedIntegrable
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.continuous_right_convolution_bounded_integrable : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (m : Measure H) (α : H → ℂ), Integrable α m → ∀ (φ : G → ℂ), Continuous φ → ∀ B : ℝ, (∀ g, ‖φ g‖ ≤ B) → Continuous (fun x => ∫ h, α h * φ (x * (h : G)) ∂m) := by
  first | exact @GlobalTheory.conv_right_continuous | exact GlobalTheory.conv_right_continuous | (intros; apply GlobalTheory.conv_right_continuous <;> assumption)
