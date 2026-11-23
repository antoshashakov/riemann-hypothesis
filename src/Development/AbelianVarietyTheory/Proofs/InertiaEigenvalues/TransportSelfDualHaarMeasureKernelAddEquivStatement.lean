module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportSelfDualHaarMeasureKernelAddEquiv
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.transport_selfDualHaarMeasureKernel_addEquiv : ∀ {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V'] (h : V' ≃+ V), Continuous h → Continuous h.symm → ∀ (μ : Measure V) (B : V → V → ℂ), ((SelfDual μ B ∧ ∀ x : V, AEMeasurable (x + ·) μ) → SelfDual (Measure.map h.symm μ) (fun x y => B (h x) (h y))) ∧ ∀ (f : V' → ℂ) (y : V'), fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y = fourB μ B (fun v => f (h.symm v)) (h y) := by
  intro V V' _ _ _ _ _ _ _ _ h hc hs μ B
  obtain ⟨htransport, hfour⟩ := GlobalTheory.transport_selfDual_fourB h hc hs μ B
  exact ⟨fun hsd => (htransport hsd).1, hfour⟩
