module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringComplexOverPrime
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.exists_valuationSubring_complex_restrict_eq_at_prime : ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)), ∃ V : ValuationSubring ℂ, ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F := by
  first | exact @GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime | exact GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime | (intros; apply GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime <;> assumption)
