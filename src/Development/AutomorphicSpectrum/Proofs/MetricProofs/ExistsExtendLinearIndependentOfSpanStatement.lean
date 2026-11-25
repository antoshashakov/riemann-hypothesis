module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsExtendLinearIndependentOfSpan
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.exists_extend_linearIndependent_of_span : ∀ (g m r : ℕ) (w : Fin r → Fin g → ℂ) (b : Fin m → Fin g → ℂ), LinearIndependent ℂ w → LinearIndependent ℂ b → (∀ a, w a ∈ Submodule.span ℂ (Set.range b)) → ∃ (k : ℕ) (J : Fin k → Fin m), r + k = m ∧ LinearIndependent ℂ (Fin.append w (fun j => b (J j))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Exchange.exists_completion_by_members | exact GlobalTheory.CompanionTheory.Ar.Exchange.exists_completion_by_members | (intros; apply GlobalTheory.CompanionTheory.Ar.Exchange.exists_completion_by_members <;> assumption)
