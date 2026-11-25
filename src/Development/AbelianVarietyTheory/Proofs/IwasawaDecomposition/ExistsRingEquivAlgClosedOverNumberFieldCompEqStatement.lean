module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivAlgClosedOverNumberFieldCompEq
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.exists_ringEquiv_algClosed_over_numberField_comp_eq : ∀ (K Ω₁ Ω₂ : Type) [Field K] [NumberField K] [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂] [CharZero Ω₁] [CharZero Ω₂] (a : K →+* Ω₁) (b : K →+* Ω₂), Cardinal.mk Ω₁ = Cardinal.mk Ω₂ → Cardinal.aleph0 < Cardinal.mk Ω₁ → ∃ ι : Ω₁ ≃+* Ω₂, ∀ x, ι (a x) = b x := by
  first | exact @GlobalTheory.AlgClosedIsoOverNumberField.exists_ringEquiv_comp_eq | exact GlobalTheory.AlgClosedIsoOverNumberField.exists_ringEquiv_comp_eq | (intros; apply GlobalTheory.AlgClosedIsoOverNumberField.exists_ringEquiv_comp_eq <;> assumption)
