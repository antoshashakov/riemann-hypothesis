module

public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardPadicAlgClPadicComplexEqComplex
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.card_padicAlgCl_padicComplex_eq_complex : ∀ (l : ℕ) [Fact l.Prime], Cardinal.mk (PadicAlgCl l) = Cardinal.mk ℂ ∧ Cardinal.mk ℂ_[l] = Cardinal.mk ℂ := by
  first | exact @GlobalTheory.PadicCard.card_padicAlgCl_padicComplex | exact GlobalTheory.PadicCard.card_padicAlgCl_padicComplex | (intros; apply GlobalTheory.PadicCard.card_padicAlgCl_padicComplex <;> assumption)
