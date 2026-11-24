module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationNatCastEqOneOfCoprime
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime : ∀ (V : ValuationSubring ℂ) (a b : ℕ), Nat.Coprime a b → V.valuation (a : ℂ) = 1 ∨ V.valuation (b : ℂ) = 1 := by
  first | exact @GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime | exact GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime | (intros; apply GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime <;> assumption)
