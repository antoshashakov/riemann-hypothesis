module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanSelfdualMeasurePi
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.archimedean_selfdual_measure_pi : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ k : Measure (Ainf F), SelfDual k (fun s t => psiInf F ψ (s * t)) → ∀ (ι : Type) [Fintype ι], SelfDual (Measure.pi fun _ : ι => k) (fun x y => psiInf F ψ (x ⬝ᵥ y)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.selfDual_pi_inf | exact GlobalTheory.CompanionTheory.SW.selfDual_pi_inf | (intros; apply GlobalTheory.CompanionTheory.SW.selfDual_pi_inf <;> assumption)
